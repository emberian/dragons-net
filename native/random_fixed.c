/* SPDX-License-Identifier: AGPL-3.0-or-later
 * For the host lane, loaded before libc: getrandom gives octets of all ones, so that the run's value
 * has its top bit and reads otherwise with a sign. */
#define _GNU_SOURCE
#include <string.h>
#include <sys/random.h>

ssize_t getrandom(void *buf, size_t n, unsigned flags) {
    (void)flags;
    memset(buf, 0xff, n);
    return (ssize_t)n;
}
