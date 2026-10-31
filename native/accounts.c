/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The accounts of AUTHINFO USER and PASS (accounts.h). PKCS5_PBKDF2_HMAC, EVP_sha256 and
 * CRYPTO_memcmp are declared from their signatures in the OpenSSL 3 manual pages. */
#define _GNU_SOURCE
#include "accounts.h"
#include "dn_session_layout.h"
#include "host.h"
#include <dlfcn.h>
#include <stdarg.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdlib.h>
#include <sys/eventfd.h>
#include <sys/random.h>
#include <sys/stat.h>

/* ITERATIONS_MIN is OWASP's count for PBKDF2-HMAC-SHA256 (Password Storage Cheat Sheet). */
enum { CONNS = DN_SESSION_CONNS, NAME_MAX_ = DN_SESSION_NAME_MAX, PASSWORD_MAX = DN_SESSION_PASSWORD_MAX, SALT_MIN = 8, SALT_MAX = 64, KEY = 32,
       ACCOUNTS_MAX = 4096, FILE_MAX = 1 << 20, ITERATIONS_MIN = 600000, ITERATIONS_MAX = 100000000 };

struct account {
    unsigned char name[NAME_MAX_], salt[SALT_MAX], key[KEY];
    size_t name_len, salt_len;
    int iterations;
};

/* A connection's check: queued in the order it came, or its verdict waiting to be given out. */
struct check {
    int queued, judged, ok;
    uint64_t gen, order;
    unsigned char name[NAME_MAX_], password[PASSWORD_MAX];
    size_t name_len, password_len;
};

static struct {
    int (*PKCS5_PBKDF2_HMAC)(const char *pass, int passlen, const unsigned char *salt, int saltlen, int iter,
                             const void *digest, int keylen, unsigned char *out);
    const void *(*EVP_sha256)(void);
    int (*CRYPTO_memcmp)(const void *a, const void *b, size_t len);
} crypto;

static struct account *accounts, unknown;
static size_t count;
static struct check checks[CONNS];
static uint64_t orders;
static int wake = -1, queued;
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t work = PTHREAD_COND_INITIALIZER;

__attribute__((format(printf, 3, 4))) static int failed(char *why, size_t why_len, const char *format, ...) {
    va_list args;
    va_start(args, format);
    vsnprintf(why, why_len, format, args);
    va_end(args);
    return 1;
}

static int hex(int c) {
    return c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : -1;
}

/* The octets the lowercase hex digits from `p` to `end` write into `out`, at most `max`; or -1. */
static long unhex(const char *p, const char *end, unsigned char *out, size_t max) {
    if ((end - p) % 2 || (size_t)(end - p) / 2 > max) return -1;
    for (size_t k = 0; p + 2 * k < end; ++k) {
        int hi = hex(p[2 * k]), lo = hex(p[2 * k + 1]);
        if (hi < 0 || lo < 0) return -1;
        out[k] = (unsigned char)(hi << 4 | lo);
    }
    return (end - p) / 2;
}

/* One line of the file into `a`: a name of visible octets but the colon, the iterations, the salt
 * and the key; zero when it is one. */
static int account_of(char *line, struct account *a) {
    char *f[4], *p = line;
    for (int k = 0; k < 4; ++k) {
        f[k] = p;
        p = k < 3 ? strchr(p, ':') : p + strlen(p);
        if (!p) return 1;
        if (k < 3) *p++ = 0;
    }
    size_t n = strlen(f[0]);
    if (n < 1 || n > NAME_MAX_) return 1;
    for (size_t k = 0; k < n; ++k)
        if (f[0][k] < 33 || f[0][k] > 126) return 1;
    memcpy(a->name, f[0], n);
    a->name_len = n;
    char *end;
    errno = 0;
    long it = strtol(f[1], &end, 10);
    if (f[1][0] < '1' || f[1][0] > '9' || *end || errno || it < ITERATIONS_MIN || it > ITERATIONS_MAX) return 1;
    a->iterations = (int)it;
    long salt = unhex(f[2], f[2] + strlen(f[2]), a->salt, SALT_MAX);
    if (salt < SALT_MIN) return 1;
    a->salt_len = (size_t)salt;
    return unhex(f[3], f[3] + strlen(f[3]), a->key, KEY) != KEY;
}

static const struct account *find(const unsigned char *name, size_t len) {
    for (size_t k = 0; k < count; ++k)
        if (accounts[k].name_len == len && !memcmp(accounts[k].name, name, len)) return &accounts[k];
    return NULL;
}

static int read_accounts(const char *path, char *why, size_t why_len) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOCTTY);
    if (fd < 0) return failed(why, why_len, "%s: %s", path, strerror(errno));
    struct stat st;
    if (fstat(fd, &st) || !S_ISREG(st.st_mode) || st.st_size > FILE_MAX) {
        close(fd);
        return failed(why, why_len, "%s: not a file of at most 1 MiB", path);
    }
    if (st.st_mode & (S_IRWXO | S_IWGRP)) {
        close(fd);
        return failed(why, why_len, "%s: others may read it, or its group write it", path);
    }
    char *text = malloc((size_t)st.st_size + 1);
    accounts = calloc(ACCOUNTS_MAX, sizeof *accounts);
    if (!text || !accounts) dn_harness("accounts: out of memory");
    size_t n = 0;
    int bad = 0;
    for (ssize_t got; n < (size_t)st.st_size && (got = read(fd, text + n, (size_t)st.st_size - n)) != 0;) {
        if (got < 0 && errno == EINTR) continue;
        if (got < 0) {
            bad = failed(why, why_len, "%s: %s", path, strerror(errno));
            break;
        }
        n += (size_t)got;
    }
    close(fd);
    text[n] = 0;
    unsigned line = 0;
    for (char *p = text, *next; !bad && p < text + n; p = next) {
        ++line;
        char *end = memchr(p, '\n', (size_t)(text + n - p));
        next = end ? end + 1 : text + n;
        size_t len = (size_t)((end ? end : text + n) - p);
        if (len && p[len - 1] == '\r') --len;
        int nul = memchr(p, 0, len) != NULL;
        p[len] = 0;
        if (!nul && (!*p || *p == '#')) continue;
        if (nul || count == ACCOUNTS_MAX ||
            account_of(p, &accounts[count]) || find(accounts[count].name, accounts[count].name_len))
            bad = failed(why, why_len, "%s:%u: not an account, or one more than 4096 or named twice", path, line);
        else ++count;
    }
    explicit_bzero(text, n);
    free(text);
    if (bad) {
        explicit_bzero(accounts, ACCOUNTS_MAX * sizeof *accounts);
        free(accounts);
        accounts = NULL;
        count = 0;
    }
    return bad;
}

static int load(char *why, size_t why_len) {
    void *lib = dlopen("libcrypto.so.3", RTLD_NOW | RTLD_LOCAL);
    if (!lib) return failed(why, why_len, "libcrypto.so.3: %s", dlerror());
    *(void **)&crypto.PKCS5_PBKDF2_HMAC = dlsym(lib, "PKCS5_PBKDF2_HMAC");
    *(void **)&crypto.EVP_sha256 = dlsym(lib, "EVP_sha256");
    *(void **)&crypto.CRYPTO_memcmp = dlsym(lib, "CRYPTO_memcmp");
    if (!crypto.PKCS5_PBKDF2_HMAC || !crypto.EVP_sha256 || !crypto.CRYPTO_memcmp)
        return failed(why, why_len, "libcrypto.so.3 lacks PKCS5_PBKDF2_HMAC, EVP_sha256 or CRYPTO_memcmp");
    return 0;
}

/* Whether the password is the account's of that name. Every check derives as many iterations as
 * the file's largest count, those an account lacks over `unknown`, so that the time tells neither
 * which names exist nor their counts. */
static int verify(const struct check *c) {
    const struct account *a = find(c->name, c->name_len), *use = a ? a : &unknown;
    unsigned char out[KEY], rest[KEY];
    int ok = crypto.PKCS5_PBKDF2_HMAC((const char *)c->password, (int)c->password_len, use->salt, (int)use->salt_len,
                                      use->iterations, crypto.EVP_sha256(), KEY, out) == 1 &&
             crypto.CRYPTO_memcmp(out, use->key, KEY) == 0 && a;
    if (use->iterations < unknown.iterations)
        crypto.PKCS5_PBKDF2_HMAC((const char *)c->password, (int)c->password_len, unknown.salt, (int)unknown.salt_len,
                                 unknown.iterations - use->iterations, crypto.EVP_sha256(), KEY, rest);
    explicit_bzero(out, sizeof out);
    explicit_bzero(rest, sizeof rest);
    return ok;
}

static void *checking(void *unused) {
    (void)unused;
    for (;;) {
        pthread_mutex_lock(&lock);
        while (!queued) pthread_cond_wait(&work, &lock);
        int at = -1;
        for (int k = 0; k < CONNS; ++k)
            if (checks[k].queued && (at < 0 || checks[k].order < checks[at].order)) at = k;
        struct check c = checks[at];
        checks[at].queued = 0;
        explicit_bzero(checks[at].password, sizeof checks[at].password);
        --queued;
        pthread_mutex_unlock(&lock);
        int ok = verify(&c);
        uint64_t gen = c.gen;
        explicit_bzero(&c, sizeof c);
        pthread_mutex_lock(&lock);
        /* A connection gone and another at its index since: the verdict is the old one's. */
        if (!checks[at].queued) checks[at] = (struct check){.judged = 1, .ok = ok, .gen = gen};
        pthread_mutex_unlock(&lock);
        uint64_t one = 1;
        if (write(wake, &one, sizeof one) != sizeof one) dn_harness_now("eventfd: %s", strerror(errno));
    }
    return NULL;
}

int dn_accounts_load(const char *path, char *why, size_t why_len) {
    if (load(why, why_len) || read_accounts(path, why, why_len)) return 1;
    /* The account no name finds: the file's largest count, with a key no password gives. */
    unknown.iterations = ITERATIONS_MIN;
    for (size_t k = 0; k < count; ++k)
        if (accounts[k].iterations > unknown.iterations) unknown.iterations = accounts[k].iterations;
    unknown.salt_len = SALT_MIN;
    if (getrandom(unknown.salt, SALT_MIN, 0) != SALT_MIN || getrandom(unknown.key, KEY, 0) != KEY)
        dn_harness("getrandom: %s", strerror(errno));
    return 0;
}

void dn_accounts_start(void) {
    wake = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
    if (wake < 0) dn_harness("eventfd: %s", strerror(errno));
    pthread_t t;
    if (pthread_create(&t, NULL, checking, NULL) || pthread_detach(t)) dn_harness("accounts: no thread");
}

int dn_accounts_fd(void) {
    return wake;
}

void dn_accounts_check(int idx, uint64_t gen, const unsigned char *name, size_t name_len,
                       const unsigned char *password, size_t password_len) {
    if (idx < 0 || idx >= CONNS || name_len > NAME_MAX_ || password_len > PASSWORD_MAX)
        dn_violation("dn_emit: a check of %zu and %zu octets for connection %d", name_len, password_len, idx);
    pthread_mutex_lock(&lock);
    struct check *c = &checks[idx];
    if (c->queued) dn_violation("dn_emit: a second check for connection %d", idx);
    *c = (struct check){.queued = 1, .gen = gen, .order = orders++, .name_len = name_len, .password_len = password_len};
    memcpy(c->name, name, name_len);
    memcpy(c->password, password, password_len);
    ++queued;
    pthread_cond_signal(&work);
    pthread_mutex_unlock(&lock);
}

void dn_accounts_forget(int idx) {
    pthread_mutex_lock(&lock);
    if (checks[idx].queued) --queued;
    explicit_bzero(&checks[idx], sizeof checks[idx]);
    pthread_mutex_unlock(&lock);
}

int dn_accounts_ready(void) {
    if (wake < 0) return 0;
    uint64_t drained;
    if (read(wake, &drained, sizeof drained) < 0 && errno != EAGAIN) dn_harness("eventfd: %s", strerror(errno));
    int found = 0;
    pthread_mutex_lock(&lock);
    for (int k = 0; k < CONNS; ++k) found |= checks[k].judged;
    pthread_mutex_unlock(&lock);
    return found;
}

int dn_accounts_verdict(int *idx, uint64_t *gen, int *ok) {
    int found = 0;
    pthread_mutex_lock(&lock);
    for (int k = 0; k < CONNS && !found; ++k)
        if (checks[k].judged) {
            *idx = k, *gen = checks[k].gen, *ok = checks[k].ok;
            checks[k].judged = 0;
            found = 1;
        }
    pthread_mutex_unlock(&lock);
    return found;
}
