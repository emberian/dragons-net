/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The accounts AUTHINFO USER and PASS log in to (RFC 4643 §2.3): a file of lines
 * `NAME:ITERATIONS:SALT:KEY`, the salt and the key in hex, the key PBKDF2-HMAC-SHA256's of the
 * password (RFC 8018 §5.2) through OpenSSL 3's libcrypto, loaded with dlopen when the file is set.
 * The checks run on a thread of their own, so that a slow one holds up no connection but its own;
 * a verdict comes back with a later batch. A name no account has is checked against one that cannot
 * match, as long as a real one, so that the time does not tell which names exist. */
#ifndef DN_ACCOUNTS_H
#define DN_ACCOUNTS_H
#include <stddef.h>
#include <stdint.h>

/* Loads libcrypto and the accounts at `path`; on failure nonzero, with the reason in `why`. A file
 * anyone but its owner and group may read, or its group write, is refused. */
int dn_accounts_load(const char *path, char *why, size_t why_len);

/* Starts the thread the checks run on. */
void dn_accounts_start(void);

/* The descriptor that is readable while a verdict waits. */
int dn_accounts_fd(void);

/* Hands the name and the password of connection `idx` at generation `gen` to the thread, which
 * keeps its own copies until the check is done and then wipes them. */
void dn_accounts_check(int idx, uint64_t gen, const unsigned char *name, size_t name_len,
                       const unsigned char *password, size_t password_len);

/* A check not begun of connection `idx` dropped: the connection is gone. */
void dn_accounts_forget(int idx);

/* Whether a verdict waits. */
int dn_accounts_ready(void);

/* The next verdict, if one waits: its connection and generation, and whether the name and the
 * password were an account's. */
int dn_accounts_verdict(int *idx, uint64_t *gen, int *ok);

#endif
