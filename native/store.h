/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The host's side of the article store (decision 0005): the spool directory, held under an exclusive
 * lock; the mark a failed sync leaves for as long as the machine runs; what the program is handed at
 * start; and which clients may post. A store refused at start ends the host with status 4. */
#ifndef DN_STORE_H
#define DN_STORE_H
#include <sys/socket.h>

/* Take a store option; 0 if `name` is none. */
int dn_store_option(const char *name, const char *value);

/* After the options: open and lock the spool, refuse a mark of this boot and remove an older one,
 * draw the random octets. */
void dn_store_start(void);

/* What the program is handed: the wall clock, the random octets, the path identity and the groups. */
void dn_store_fill(unsigned char *next);

/* The spool's directory, -1 without a store. */
int dn_store_spool(void);

/* Leave the mark of a failed sync, of this boot, in the spool and the run directory; the host ends if
 * it is left in neither. Safe from any thread. */
void dn_store_mark_failed(void);

/* Whether a client at `peer` may post: never without a spool. */
int dn_store_may_post(const struct sockaddr_storage *peer);

#endif
