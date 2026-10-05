/* SPDX-License-Identifier: AGPL-3.0-or-later
 * A point of failure as the host's test build carries them, for the fiu lane: for each line it
 * reads, whether the point `dn/probe` fails and, when it does, the information it was enabled
 * with. Built without FIU_ENABLE, the point is no code at all. */
#include <fiu-local.h>
#include <stdint.h>
#include <stdio.h>

int main(void) {
    char line[64];
    if (setvbuf(stdout, NULL, _IOLBF, 0)) return 2;
    while (fgets(line, sizeof line, stdin)) {
        int failed = fiu_fail("dn/probe") != 0;
        unsigned long info = failed ? (unsigned long)(uintptr_t)fiu_failinfo() : 0;
        if (printf("%d %lu\n", failed, info) < 0) return 2;
    }
    return 0;
}
