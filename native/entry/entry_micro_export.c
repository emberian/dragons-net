/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The exported design without a network: this host runs the loop and calls the program's
 * exported functions, with its buffers in its own memory, as the native lanes do.
 *   nop N       N calls of an exported function that adds one
 *   reply N     N commands, every reply checked */
#include "entry.h"
extern uint32_t dn_reply(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint32_t dn_nop(uint64_t);

int main(int argc, char **argv) {
    if (argc != 3) dn_fail("usage: entry-micro-export nop N | reply N");
    long n = dn_number(argv[2], 1, 1000000000);
    dn_runtime_setup();
    dn_runtime_header();
    cml_main();
    if (!dn_runtime_header_intact()) dn_fail("the heap header is not what the compiler theorem requires");
    if (strcmp(argv[1], "nop") == 0) {
        uint32_t acc = 0;
        double start = dn_now_ns();
        for (long i = 0; i < n; ++i) acc = dn_nop(acc);
        double end = dn_now_ns();
        if (acc != (uint32_t)n) dn_fail("the exported function did not add one each time");
        printf("{\"design\":\"export\",\"work\":\"nop\",\"calls\":%ld,\"ns_per_call\":%.2f}\n", n, (end - start) / (double)n);
    } else if (strcmp(argv[1], "reply") == 0) {
        static unsigned char in[DN_ENTRY_COMMANDS][DN_ENTRY_DATA], out[DN_ENTRY_DATA];
        for (int c = 0; c < DN_ENTRY_COMMANDS; ++c)
            memcpy(in[c], dn_entry_commands[c], (size_t)dn_entry_command_lengths[c]);
        double start = dn_now_ns();
        for (long i = 0; i < n; ++i) {
            int c = (int)(i % DN_ENTRY_COMMANDS);
            uint32_t len = dn_reply((uintptr_t)in[c], (uint64_t)dn_entry_command_lengths[c], (uintptr_t)out, DN_ENTRY_DATA);
            if (len != (uint32_t)dn_entry_reply_lengths[c] || memcmp(out, dn_entry_replies[c], len))
                dn_fail("a reply is not the one the reference gives");
        }
        double end = dn_now_ns();
        printf("{\"design\":\"export\",\"work\":\"reply\",\"events\":%ld,\"batch\":1,\"ns_per_event\":%.2f}\n", n, (end - start) / (double)n);
    } else {
        dn_fail("usage: entry-micro-export nop N | reply N");
    }
    return 0;
}
