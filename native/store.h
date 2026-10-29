/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The host's side of the article store (decision 0005): the spool directory, held under an exclusive
 * lock; the mark a failed sync leaves for as long as the machine runs; what the program is handed at
 * start; and which clients may post. A store refused at start ends the host with status 4. */
#ifndef DN_STORE_H
#define DN_STORE_H
#include <stdint.h>
#include <stdio.h>
#include <sys/socket.h>

/* Take a store option; 0 if `name` is none. The host refuses one given twice that is taken once. */
int dn_store_option(const char *name, const char *value);

/* After the options, without starting anything: check them together and that the spool and the run
 * directory open as directories. */
void dn_store_check(void);

/* Once checked, the options as members of a JSON object on `out`, each after a comma, the networks
 * that may post as given or by default. */
void dn_store_settings(FILE *out);

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

/* The run stopped by recovery at start, `stop` its code: why, from recovery's area `rec`, or the
 * class of the file job that failed; the host ends with status 4. */
__attribute__((noreturn)) void dn_store_recovery_stopped(uint64_t stop, const unsigned char *rec, uint64_t job_class);

/* Whether a client at `peer` may post: never without a spool. */
int dn_store_may_post(const struct sockaddr_storage *peer);

/* With a spool, log a connection opened, whose address the program never sees, numbered among the
 * run's from one as Injection-Info's `logging-data` names it: `connection RUN.NUMBER from ADDRESS
 * port PORT`. A line stderr cannot take at once is counted, `connections not logged: N`, before the
 * next that goes. */
void dn_store_log_opened(const struct sockaddr_storage *peer);

#endif
