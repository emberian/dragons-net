/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The loop design without a network: the program's main runs the loop and fetches events from
 * this host through external calls, into its own heap.
 *   nop N           N empty external calls (the loop-nop program)
 *   reply N K       N commands in batches of K, every reply checked, and nothing written outside
 *                   the batch areas (the loop program)
 *   hostile CASE    a batch the program has to refuse on its own: 1 more events than a batch
 *                   holds, 2 a negative count, 3 a length past the slot, 4 a negative length
 *   header          the five heap words as written, relative to cake_text_begin, for the check
 *                   that recomputes them from the assembly
 * With --no-header the host leaves the heap header unwritten, which the first call has to notice. */
#include "entry.h"
extern char cake_text_begin[];

static long remaining, batch, next_command, hostile;
static uint64_t emitted, nops, config;

void ffidn_config(unsigned char *c, long clen, unsigned char *a, long alen) {
    dn_in_heap(c, clen, "config");
    dn_in_heap(a, alen, "config");
    dn_header_checked();
    if (alen != 8) dn_fail("config: the array is not one word");
    dn_put_word(a, config);
}

void ffidn_nop(unsigned char *c, long clen, unsigned char *a, long alen) {
    (void)c; (void)clen; (void)a; (void)alen;
    ++nops;
}

static void fill_slots(unsigned char *a, long k) {
    for (long i = 0; i < k; ++i) {
        unsigned char *slot = a + 8 + i * DN_ENTRY_SLOT;
        long command = next_command++ % DN_ENTRY_COMMANDS;
        dn_put_word(slot, (uint64_t)command);
        dn_put_word(slot + 8, (uint64_t)dn_entry_command_lengths[command]);
        memcpy(slot + 16, dn_entry_commands[command], (size_t)dn_entry_command_lengths[command]);
    }
}

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen) {
    dn_in_heap(c, clen, "next");
    dn_in_heap(a, alen, "next");
    dn_header_checked();
    if (alen != DN_ENTRY_AREA) dn_fail("next: the array is not a batch area");
    if (hostile) {
        /* The host writes only its array; a count past it points the program at the fill. */
        fill_slots(a, DN_ENTRY_BATCH_MAX);
        uint64_t count[] = {DN_ENTRY_BATCH_MAX + 1, UINT64_MAX, 8, 8};
        dn_put_word(a, count[hostile - 1]);
        if (hostile == 3) dn_put_word(a + 16, DN_ENTRY_DATA + 1);
        if (hostile == 4) dn_put_word(a + 16, UINT64_MAX);
        return;
    }
    long k = remaining < batch ? remaining : batch;
    dn_put_word(a, (uint64_t)k);
    fill_slots(a, k);
    remaining -= k;
}

void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen) {
    dn_in_heap(c, clen, "emit");
    dn_in_heap(a, alen, "emit");
    if (alen != DN_ENTRY_AREA) dn_fail("emit: the array is not a batch area");
    if (hostile) {
        if (!dn_fill_intact()) dn_fail("the program wrote outside its batch areas");
        dn_fail("the program answered a hostile batch");
    }
    uint64_t k = dn_word(a);
    if (k > DN_ENTRY_BATCH_MAX) dn_fail("emit: more replies than a batch holds");
    for (uint64_t i = 0; i < k; ++i) {
        const unsigned char *slot = a + 8 + i * DN_ENTRY_SLOT;
        uint64_t command = dn_word(slot), len = dn_word(slot + 8);
        if (command >= DN_ENTRY_COMMANDS || len != (uint64_t)dn_entry_reply_lengths[command] ||
            memcmp(slot + 16, dn_entry_replies[command], len))
            dn_fail("emit: a reply is not the one the reference gives");
        ++emitted;
    }
}

static void usage(void) {
    dn_fail("usage: entry-micro-loop nop N | reply N K | hostile CASE | header [--no-header]");
}

int main(int argc, char **argv) {
    int header = !(argc > 1 && strcmp(argv[argc - 1], "--no-header") == 0);
    if (!header) --argc;
    if (argc < 2) usage();
    dn_runtime_setup();
    if (header) dn_runtime_header();
    if (strcmp(argv[1], "header") == 0 && argc == 2) {
        printf("{\"header\":[");
        for (int i = 0; i < 5; ++i) {
            uintptr_t word = (uintptr_t)dn_word((const unsigned char *)cml_heap + 8 * i);
            printf("%s%" PRIdPTR, i ? "," : "", (intptr_t)(word - (uintptr_t)cake_text_begin));
        }
        printf("]}\n");
    } else if (strcmp(argv[1], "hostile") == 0 && argc == 3) {
        hostile = dn_number(argv[2], 1, 4);
        dn_fill_heap();
        cml_main();
        if (!dn_fill_intact()) dn_fail("the program wrote outside its batch areas");
        printf("{\"design\":\"loop\",\"work\":\"hostile\",\"case\":%ld,\"stopped\":true}\n", hostile);
    } else if (strcmp(argv[1], "nop") == 0 && argc == 3) {
        long n = dn_number(argv[2], 1, 1000000000);
        config = (uint64_t)n;
        double start = dn_now_ns();
        cml_main();
        double end = dn_now_ns();
        if (nops != (uint64_t)n) dn_fail("the program made another number of calls");
        printf("{\"design\":\"loop\",\"work\":\"nop\",\"calls\":%ld,\"ns_per_call\":%.2f}\n", n, (end - start) / (double)n);
    } else if (strcmp(argv[1], "reply") == 0 && argc == 4) {
        long n = dn_number(argv[2], 1, 1000000000);
        batch = dn_number(argv[3], 1, DN_ENTRY_BATCH_MAX);
        remaining = n;
        dn_fill_heap();
        double start = dn_now_ns();
        cml_main();
        double end = dn_now_ns();
        if (emitted != (uint64_t)n) dn_fail("the program answered another number of commands");
        if (!dn_fill_intact()) dn_fail("the program wrote outside its batch areas");
        printf("{\"design\":\"loop\",\"work\":\"reply\",\"events\":%ld,\"batch\":%ld,\"ns_per_event\":%.2f}\n", n, batch, (end - start) / (double)n);
    } else {
        usage();
    }
    return 0;
}
