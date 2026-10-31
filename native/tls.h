/* SPDX-License-Identifier: AGPL-3.0-or-later
 * TLS for the NNTP host, implicit as RFC 8143 has it: every connection of a listener given a
 * certificate speaks TLS from its first octet. OpenSSL 3's libssl does the protocol; tls.c loads it
 * when a certificate is set, so the host builds without its headers and a server without TLS never
 * loads it. Every call works on a nonblocking socket and says what it waits for. */
#ifndef DN_TLS_H
#define DN_TLS_H

#include <stddef.h>

struct dn_tls;

/* What a call left: done, or waiting until the socket can be read or written, or the connection is
 * over: its peer ended it cleanly, or it failed. */
enum dn_tls_state { DN_TLS_DONE, DN_TLS_WANT_READ, DN_TLS_WANT_WRITE, DN_TLS_ENDED, DN_TLS_FAILED };

/* Loads libssl and makes the server's context from the certificate chain and the key, PEM files,
 * the key's file not one others may read or its group write, and the key under no passphrase; TLS
 * 1.2 at least, no renegotiation, no session cache; ciphers and their security level are libssl's
 * defaults. On failure it returns nonzero with the reason in `why`. */
int dn_tls_setup(const char *certificate, const char *key, char *why, size_t why_len);

/* A server side for the connected socket `fd`, or NULL. */
struct dn_tls *dn_tls_new(int fd);

/* One step of the handshake. */
enum dn_tls_state dn_tls_handshake(struct dn_tls *t);

/* Up to `len` decrypted octets into `buffer`: how many, with DN_TLS_DONE, or 0 and the state. */
size_t dn_tls_read(struct dn_tls *t, unsigned char *buffer, size_t len, enum dn_tls_state *state);

/* Up to `len` octets of `buffer` taken to send: how many, with DN_TLS_DONE, or 0 and the state. A
 * write that waited is to be made again with the same octets first, as the session does. */
size_t dn_tls_write(struct dn_tls *t, const unsigned char *buffer, size_t len, enum dn_tls_state *state);

/* Why the last call that failed did, as OpenSSL says: no address, nothing a client sent. */
const char *dn_tls_reason(void);

/* Whether decrypted octets wait, which no poll will report. */
int dn_tls_pending(struct dn_tls *t);

/* Says that this side has finished, if `gracefully`, and frees the connection's TLS; the socket
 * stays the caller's. */
void dn_tls_end(struct dn_tls *t, int gracefully);

#endif
