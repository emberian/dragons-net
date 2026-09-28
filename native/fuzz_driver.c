/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Host for generated programs (scripts/native_fuzz.py). Each line of stdin is one call:
 *
 *   FN SEED MASK ENTRIES (BUFFER OFFSET)... PARAMS (d VALUE | p BUFFER OFFSET | t)...
 *
 * The three data buffers are filled with SplitMix64 from SEED, masked, the page of pointers
 * gets the real address of each entry, and the function is called with the parameters and
 * the result slot. Each buffer, the page of pointers and the page of the slot sit between
 * two pages without access; the page of pointers is read-only during the call, and the rest
 * of the slot's page has to stay as it was. One line is printed for each call:
 *
 *   STATUS RESULT CHANGED (BUFFER OFFSET VALUE)...
 *
 * with every word of the buffers that differs from its fill. A call that touches a page
 * without access ends the process, and so does one still running after a tenth of a second,
 * far longer than any generated program takes; the lines printed before it say which call it
 * was. */
#define _GNU_SOURCE
#include "cake_runtime.h"
#include "host.h"
#include <inttypes.h>
#include <sys/time.h>

enum { PAGE = 4096, BUFFERS = 3, WORDS = PAGE / 8, SLOT_FILL = 0xa5, LIMIT_US = 100000 };

/* Generated with the programs: calls function FN with COUNT arguments, the last the slot, and
   returns nonzero when there is no such function. */
int dn_fuzz_call(size_t fn, const uint64_t *args, size_t count, uint32_t *status);

static uint64_t mix(uint64_t z) {
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

/* Output I (from zero) of SplitMix64 started at SEED. */
static uint64_t splitmix(uint64_t seed, uint64_t i) {
    return mix(seed + 0x9e3779b97f4a7c15ULL * (i + 1));
}

static uint64_t fill(uint64_t seed, uint64_t mask, size_t b, size_t i) {
    return splitmix(seed, b * WORDS + i) & mask;
}

static int number(uint64_t *out) {
    char text[32];
    if (scanf("%31s", text) != 1) return 0;
    *out = dn_parse_u64(text, UINT64_MAX);
    return 1;
}

/* Once armed, the default action of SIGALRM ends the process. */
static void timer(long microseconds) {
    struct itimerval limit = {{0, 0}, {0, microseconds}};
    if (setitimer(ITIMER_REAL, &limit, NULL)) dn_harness("setitimer: %s", strerror(errno));
}

static uint64_t need(void) {
    uint64_t value;
    if (!number(&value)) dn_harness("bad input: a truncated call");
    return value;
}

int main(void) {
    if (dn_page_size() != PAGE) dn_harness("the host expects 4 KiB pages");
    dn_expect_faults();
    dn_runtime_init();
    unsigned char *buffer[BUFFERS], *table = dn_guarded(), *slot_page = dn_guarded();
    for (size_t b = 0; b < BUFFERS; ++b) buffer[b] = dn_guarded();
    unsigned char *slot = slot_page + PAGE - 8;
    uint64_t fn;
    while (number(&fn)) {
        uint64_t seed = need(), mask = need(), entries = need();
        if (entries > WORDS) dn_harness("bad input: more entries than the page of pointers holds");
        for (size_t b = 0; b < BUFFERS; ++b)
            for (size_t i = 0; i < WORDS; ++i) dn_put_word(buffer[b] + 8 * i, fill(seed, mask, b, i));
        dn_protect(table, PROT_READ | PROT_WRITE);
        memset(table, 0, PAGE);
        for (size_t k = 0; k < entries; ++k) {
            uint64_t b = need(), offset = need();
            if (b >= BUFFERS || offset >= PAGE) dn_harness("bad input: an entry outside the buffers");
            dn_put_word(table + 8 * k, (uint64_t)(uintptr_t)buffer[b] + offset);
        }
        dn_protect(table, PROT_READ);
        uint64_t count = need(), args[4];
        if (count > 3) dn_harness("bad input: more than three parameters");
        for (size_t k = 0; k < count; ++k) {
            char kind[2];
            if (scanf("%1s", kind) != 1) dn_harness("bad input: a truncated parameter");
            if (kind[0] == 'd') args[k] = need();
            else if (kind[0] == 't') args[k] = (uint64_t)(uintptr_t)table;
            else if (kind[0] == 'p') {
                uint64_t b = need(), offset = need();
                if (b >= BUFFERS || offset >= PAGE) dn_harness("bad input: a pointer outside the buffers");
                args[k] = (uint64_t)(uintptr_t)buffer[b] + offset;
            } else dn_harness("bad input: an unknown kind of parameter");
        }
        memset(slot_page, SLOT_FILL, PAGE);
        args[count] = (uint64_t)(uintptr_t)slot;
        uint32_t status;
        timer(LIMIT_US);
        int unknown = dn_fuzz_call(fn, args, count + 1, &status);
        timer(0);
        if (unknown) dn_harness("no function %" PRIu64 " with %" PRIu64 " parameters", fn, count);
        for (size_t i = 0; i < PAGE - 8; ++i)
            if (slot_page[i] != SLOT_FILL)
                dn_violation("call of function %" PRIu64 " wrote beside the result slot", fn);
        size_t changed = 0;
        for (size_t b = 0; b < BUFFERS; ++b)
            for (size_t i = 0; i < WORDS; ++i)
                changed += dn_word(buffer[b] + 8 * i) != fill(seed, mask, b, i);
        printf("%" PRIu32 " %" PRIu64 " %zu", status, dn_word(slot), changed);
        for (size_t b = 0; b < BUFFERS; ++b)
            for (size_t i = 0; i < WORDS; ++i) {
                uint64_t w = dn_word(buffer[b] + 8 * i);
                if (w != fill(seed, mask, b, i)) printf(" %zu %zu %" PRIu64, b, 8 * i, w);
            }
        putchar('\n');
        if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
    }
    if (!feof(stdin)) dn_harness("bad input: unreadable");
    return 0;
}
