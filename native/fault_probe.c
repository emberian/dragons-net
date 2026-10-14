/* SPDX-License-Identifier: AGPL-3.0-or-later
 * A point of failure as the host's test build carries them, through faults.h, for the fiu lane: for
 * each line it reads, whether the point `dn/probe` fails and, when it does, the information it was
 * enabled with. Built without FIU_ENABLE, the point is no code at all. */
#include "faults.h"
#include <stdint.h>
#include <stdio.h>

int main(void) {
    char line[64];
    if (setvbuf(stdout, NULL, _IOLBF, 0)) return 2;
    while (fgets(line, sizeof line, stdin)) {
        uint64_t info = 0;
        int failed = DN_FAULT_INFO("dn/probe", info);
        if (printf("%d %llu\n", failed, (unsigned long long)info) < 0) return 2;
    }
    return 0;
}
