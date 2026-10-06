/* SPDX-License-Identifier: AGPL-3.0-or-later
 * File jobs (decision 0005): the program hands a job in a slot of dn_emit; a worker thread carries
 * its operations out in order on the spool, stopped at the first that fails, and the completion
 * comes back in a later dn_next. Files stay open across jobs, each in a place named with a
 * generation. A job that breaks the contract ends the host with status 1. */
#ifndef DN_JOBS_H
#define DN_JOBS_H

/* Start the workers on the spool's directory, -1 for none; the descriptor that is readable while a
 * completion waits, -1 without a store. */
int dn_jobs_start(int spool);

/* Take the jobs of the dn_emit array `a`, inside the call. */
void dn_jobs_take(const unsigned char *a);

/* Whether a completion waits to be handed. */
int dn_jobs_ready(void);

/* Hand the completions into the dn_next array `a`, inside the call. */
void dn_jobs_give(unsigned char *a);

#endif
