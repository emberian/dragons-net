/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The host's TLS through OpenSSL 3's libssl, loaded with dlopen when a certificate is configured
 * (tls.h). The functions are declared here from their signatures in the OpenSSL 3 manual pages,
 * and the constants are those of its headers: SSL_CTX_set_mode and SSL_CTX_set_min_proto_version
 * are macros over SSL_CTX_ctrl. */
#define _GNU_SOURCE
#include "tls.h"
#include <dlfcn.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum {
    SSL_FILETYPE_PEM = 1,
    SSL_CTRL_MODE = 33,
    SSL_CTRL_SET_SESS_CACHE_MODE = 44,
    SSL_SESS_CACHE_OFF = 0,
    SSL_CTRL_SET_MIN_PROTO_VERSION = 123,
    TLS1_2_VERSION = 0x0303,
    SSL_MODE_ENABLE_PARTIAL_WRITE = 0x1,
    SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER = 0x2,
    SSL_ERROR_WANT_READ = 2,
    SSL_ERROR_WANT_WRITE = 3,
    SSL_ERROR_ZERO_RETURN = 6,
};
#define SSL_OP_IGNORE_UNEXPECTED_EOF ((uint64_t)1 << 7)
#define SSL_OP_NO_RENEGOTIATION ((uint64_t)1 << 30)

static struct {
    const void *(*TLS_server_method)(void);
    void *(*SSL_CTX_new)(const void *method);
    long (*SSL_CTX_ctrl)(void *ctx, int cmd, long larg, void *parg);
    uint64_t (*SSL_CTX_set_options)(void *ctx, uint64_t options);
    int (*SSL_CTX_use_certificate_chain_file)(void *ctx, const char *file);
    int (*SSL_CTX_use_PrivateKey_file)(void *ctx, const char *file, int type);
    void *(*SSL_new)(void *ctx);
    int (*SSL_set_fd)(void *ssl, int fd);
    void (*SSL_set_accept_state)(void *ssl);
    int (*SSL_do_handshake)(void *ssl);
    int (*SSL_read_ex)(void *ssl, void *buf, size_t num, size_t *readbytes);
    int (*SSL_write_ex)(void *ssl, const void *buf, size_t num, size_t *written);
    int (*SSL_get_error)(const void *ssl, int ret);
    int (*SSL_pending)(const void *ssl);
    int (*SSL_shutdown)(void *ssl);
    void (*SSL_free)(void *ssl);
    unsigned long (*ERR_get_error)(void);
    void (*ERR_error_string_n)(unsigned long e, char *buf, size_t len);
    void (*ERR_clear_error)(void);
} ossl;

static void *context;
/* Why the last call that failed did, as OpenSSL says. */
static char reason[256];

struct dn_tls { void *ssl; };

/* The functions of `ossl`, looked up in libssl, whose dependencies give libcrypto's. */
static int load(char *why, size_t why_len) {
    void *lib = dlopen("libssl.so.3", RTLD_NOW | RTLD_LOCAL);
    if (!lib) {
        snprintf(why, why_len, "libssl.so.3: %s", dlerror());
        return 1;
    }
#define FIND(name)                                                                                              \
    do {                                                                                                        \
        *(void **)&ossl.name = dlsym(lib, #name);                                                               \
        if (!ossl.name) {                                                                                       \
            snprintf(why, why_len, "libssl.so.3 has no %s", #name);                                             \
            return 1;                                                                                           \
        }                                                                                                       \
    } while (0)
    FIND(TLS_server_method);
    FIND(SSL_CTX_new);
    FIND(SSL_CTX_ctrl);
    FIND(SSL_CTX_set_options);
    FIND(SSL_CTX_use_certificate_chain_file);
    FIND(SSL_CTX_use_PrivateKey_file);
    FIND(SSL_new);
    FIND(SSL_set_fd);
    FIND(SSL_set_accept_state);
    FIND(SSL_do_handshake);
    FIND(SSL_read_ex);
    FIND(SSL_write_ex);
    FIND(SSL_get_error);
    FIND(SSL_pending);
    FIND(SSL_shutdown);
    FIND(SSL_free);
    FIND(ERR_get_error);
    FIND(ERR_error_string_n);
    FIND(ERR_clear_error);
#undef FIND
    return 0;
}

/* The reason OpenSSL gives for what just failed, after `what`. */
static int failed(const char *what, char *why, size_t why_len) {
    char reason[256] = "no reason given";
    unsigned long e = ossl.ERR_get_error();
    if (e) ossl.ERR_error_string_n(e, reason, sizeof reason);
    snprintf(why, why_len, "%s: %s", what, reason);
    ossl.ERR_clear_error();
    return 1;
}

int dn_tls_setup(const char *certificate, const char *key, char *why, size_t why_len) {
    if (load(why, why_len)) return 1;
    context = ossl.SSL_CTX_new(ossl.TLS_server_method());
    if (!context) return failed("SSL_CTX_new", why, why_len);
    if (!ossl.SSL_CTX_ctrl(context, SSL_CTRL_SET_MIN_PROTO_VERSION, TLS1_2_VERSION, NULL))
        return failed("TLS 1.2 at least", why, why_len);
    ossl.SSL_CTX_ctrl(context, SSL_CTRL_MODE, SSL_MODE_ENABLE_PARTIAL_WRITE | SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER, NULL);
    /* A peer that closes the socket without saying it has finished ends its input, as over TCP; a
     * command or an article still needs its own end, which only the peer can send. */
    ossl.SSL_CTX_set_options(context, SSL_OP_NO_RENEGOTIATION | SSL_OP_IGNORE_UNEXPECTED_EOF);
    /* No session kept on the server's side: a client that resumes takes a ticket, which holds its own
     * state, so memory does not grow with the clients. */
    ossl.SSL_CTX_ctrl(context, SSL_CTRL_SET_SESS_CACHE_MODE, SSL_SESS_CACHE_OFF, NULL);
    if (ossl.SSL_CTX_use_certificate_chain_file(context, certificate) != 1)
        return failed(certificate, why, why_len);
    /* A key that is not the certificate's fails here too. */
    if (ossl.SSL_CTX_use_PrivateKey_file(context, key, SSL_FILETYPE_PEM) != 1) return failed(key, why, why_len);
    return 0;
}

struct dn_tls *dn_tls_new(int fd) {
    struct dn_tls *t = malloc(sizeof *t);
    if (!t) return NULL;
    t->ssl = ossl.SSL_new(context);
    if (!t->ssl || ossl.SSL_set_fd(t->ssl, fd) != 1) {
        if (t->ssl) ossl.SSL_free(t->ssl);
        free(t);
        ossl.ERR_clear_error();
        return NULL;
    }
    ossl.SSL_set_accept_state(t->ssl);
    return t;
}

/* What a call that returned `ret` left; of a failure, its reason is kept for `dn_tls_reason`. */
static enum dn_tls_state state_of(struct dn_tls *t, int ret) {
    int e = ossl.SSL_get_error(t->ssl, ret);
    if (e != SSL_ERROR_WANT_READ && e != SSL_ERROR_WANT_WRITE && e != SSL_ERROR_ZERO_RETURN) {
        unsigned long code = ossl.ERR_get_error();
        if (code) ossl.ERR_error_string_n(code, reason, sizeof reason);
        else snprintf(reason, sizeof reason, "the connection failed (%s)", errno ? strerror(errno) : "no reason given");
    }
    ossl.ERR_clear_error();
    switch (e) {
    case SSL_ERROR_WANT_READ: return DN_TLS_WANT_READ;
    case SSL_ERROR_WANT_WRITE: return DN_TLS_WANT_WRITE;
    case SSL_ERROR_ZERO_RETURN: return DN_TLS_ENDED;
    default: return DN_TLS_FAILED;
    }
}

/* OpenSSL reads the error queue to tell why a call failed, so a call starts with it empty. */
enum dn_tls_state dn_tls_handshake(struct dn_tls *t) {
    ossl.ERR_clear_error();
    errno = 0;
    int ret = ossl.SSL_do_handshake(t->ssl);
    if (ret == 1) return DN_TLS_DONE;
    enum dn_tls_state s = state_of(t, ret);
    return s == DN_TLS_ENDED ? DN_TLS_FAILED : s;
}

size_t dn_tls_read(struct dn_tls *t, unsigned char *buffer, size_t len, enum dn_tls_state *state) {
    size_t n = 0;
    ossl.ERR_clear_error();
    errno = 0;
    int ret = ossl.SSL_read_ex(t->ssl, buffer, len, &n);
    *state = ret == 1 ? DN_TLS_DONE : state_of(t, ret);
    return ret == 1 ? n : 0;
}

size_t dn_tls_write(struct dn_tls *t, const unsigned char *buffer, size_t len, enum dn_tls_state *state) {
    size_t n = 0;
    ossl.ERR_clear_error();
    errno = 0;
    int ret = ossl.SSL_write_ex(t->ssl, buffer, len, &n);
    *state = ret == 1 ? DN_TLS_DONE : state_of(t, ret);
    return ret == 1 ? n : 0;
}

const char *dn_tls_reason(void) {
    return reason;
}

int dn_tls_pending(struct dn_tls *t) {
    return ossl.SSL_pending(t->ssl) > 0;
}

void dn_tls_end(struct dn_tls *t, int gracefully) {
    if (gracefully) ossl.SSL_shutdown(t->ssl);
    ossl.ERR_clear_error();
    ossl.SSL_free(t->ssl);
    free(t);
}
