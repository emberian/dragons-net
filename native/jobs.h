/* SPDX-License-Identifier: AGPL-3.0-or-later
 * File jobs (decision 0005): the program hands a job in a slot of dn_emit; a worker thread carries
 * its operations out in order on the spool, stopped at the first that fails, and the completion
 * comes back in a later dn_next. Files stay open across jobs, each in a place named with a
 * generation. A job that breaks the contract ends the host with status 1. */
#ifndef DN_JOBS_H
#define DN_JOBS_H
#include <stdint.h>

/* Start the workers on the spool's directory, -1 for none; the descriptor that is readable while a
 * completion waits, -1 without a store. */
int dn_jobs_start(int spool);

/* Take the jobs of the dn_emit array `a`, inside the call. */
void dn_jobs_take(const unsigned char *a);

/* Whether a completion waits to be handed. */
int dn_jobs_ready(void);

/* Hand the completions into the dn_next array `a`, inside the call. */
void dn_jobs_give(unsigned char *a);

/* How many jobs have finished, and of them how many failed for want of space, on an I/O error and
 * on another error; an operation that finds a file there or not is not a failure. */
void dn_jobs_counted(uint64_t counts[4]);

/* At a stop: the jobs not begun dropped, those running waited for, at most `ms` milliseconds, and
 * then, none running, every file closed. `counts` takes how many were running, how many dropped and
 * how many still run; the last is returned. */
int dn_jobs_drain(uint64_t ms, int counts[3]);

#endif
