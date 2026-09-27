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
 * without access ends the process, and so does one still running after a tenth of a second, far longer
 * than any generated program takes; the lines printed before it say which call it was. */
#define _GNU_SOURCE
#include "cake_runtime.h"
#include <errno.h>
#include <inttypes.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <unistd.h>

enum { PAGE = 4096, BUFFERS = 3, WORDS = PAGE / 8, SLOT_FILL = 0xa5, LIMIT_US = 100000 };

/* Generated with the programs: calls function FN with COUNT arguments, the last the slot. */
int dn_fuzz_call(size_t fn, const uint64_t *args, size_t count, uint32_t *status);

static void protect(unsigned char *page, int access) {
    if (mprotect(page, PAGE, access)) {
        perror("mprotect");
        exit(2);
    }
}

/* The middle one of three pages; the outer two have no access. */
static unsigned char *guarded(void) {
    unsigned char *pages = mmap(NULL, 3 * PAGE, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (pages == MAP_FAILED) {
        perror("mmap");
        exit(2);
    }
    protect(pages + PAGE, PROT_READ | PROT_WRITE);
    return pages + PAGE;
}

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
    char *end;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (errno || *end || text[0] == '-') {
        fprintf(stderr, "not a number: %s\n", text);
        exit(2);
    }
    *out = value;
    return 1;
}

static void refuse(const char *what) {
    fprintf(stderr, "bad input: %s\n", what);
    exit(2);
}

/* Once armed, the default action of SIGALRM ends the process. */
static void timer(long microseconds) {
    struct itimerval limit = {{0, 0}, {0, microseconds}};
    if (setitimer(ITIMER_REAL, &limit, NULL)) {
        perror("setitimer");
        exit(2);
    }
}

static uint64_t need(void) {
    uint64_t value;
    if (!number(&value)) {
        fputs("truncated call\n", stderr);
        exit(2);
    }
    return value;
}

static uint64_t word_at(const unsigned char *page, size_t i) {
    uint64_t w;
    memcpy(&w, page + 8 * i, 8);
    return w;
}

int main(void) {
    if (sysconf(_SC_PAGESIZE) != PAGE) {
        fputs("the host expects 4 KiB pages\n", stderr);
        return 2;
    }
    dn_runtime_init();
    unsigned char *buffer[BUFFERS], *table = guarded(), *slot_page = guarded();
    for (size_t b = 0; b < BUFFERS; ++b) buffer[b] = guarded();
    unsigned char *slot = slot_page + PAGE - 8;
    uint64_t fn;
    while (number(&fn)) {
        uint64_t seed = need(), mask = need(), entries = need();
        if (entries > WORDS) refuse("more entries than the page of pointers holds");
        for (size_t b = 0; b < BUFFERS; ++b)
            for (size_t i = 0; i < WORDS; ++i) {
                uint64_t w = fill(seed, mask, b, i);
                memcpy(buffer[b] + 8 * i, &w, 8);
            }
        protect(table, PROT_READ | PROT_WRITE);
        memset(table, 0, PAGE);
        for (size_t k = 0; k < entries; ++k) {
            uint64_t b = need(), offset = need();
            if (b >= BUFFERS || offset >= PAGE) refuse("an entry outside the buffers");
            uint64_t address = (uint64_t)(uintptr_t)buffer[b] + offset;
            memcpy(table + 8 * k, &address, 8);
        }
        protect(table, PROT_READ);
        uint64_t count = need(), args[4];
        if (count > 3) refuse("more than three parameters");
        for (size_t k = 0; k < count; ++k) {
            char kind[2];
            if (scanf("%1s", kind) != 1) refuse("a truncated parameter");
            if (kind[0] == 'd') args[k] = need();
            else if (kind[0] == 't') args[k] = (uint64_t)(uintptr_t)table;
            else if (kind[0] == 'p') {
                uint64_t b = need(), offset = need();
                if (b >= BUFFERS || offset >= PAGE) refuse("a pointer outside the buffers");
                args[k] = (uint64_t)(uintptr_t)buffer[b] + offset;
            } else refuse("an unknown kind of parameter");
        }
        memset(slot_page, SLOT_FILL, PAGE);
        args[count] = (uint64_t)(uintptr_t)slot;
        uint32_t status;
        timer(LIMIT_US);
        int known = dn_fuzz_call(fn, args, count + 1, &status);
        timer(0);
        if (known) {
            fprintf(stderr, "no function %" PRIu64 " with %" PRIu64 " parameters\n", fn, count);
            return 2;
        }
        for (size_t i = 0; i < PAGE - 8; ++i)
            if (slot_page[i] != SLOT_FILL) {
                fprintf(stderr, "call of function %" PRIu64 " wrote beside the result slot\n", fn);
                return 1;
            }
        size_t changed = 0;
        for (size_t b = 0; b < BUFFERS; ++b)
            for (size_t i = 0; i < WORDS; ++i) changed += word_at(buffer[b], i) != fill(seed, mask, b, i);
        printf("%" PRIu32 " %" PRIu64 " %zu", status, word_at(slot, 0), changed);
        for (size_t b = 0; b < BUFFERS; ++b)
            for (size_t i = 0; i < WORDS; ++i) {
                uint64_t w = word_at(buffer[b], i);
                if (w != fill(seed, mask, b, i)) printf(" %zu %zu %" PRIu64, b, 8 * i, w);
            }
        putchar('\n');
        if (fflush(stdout)) {
            perror("stdout");
            return 2;
        }
    }
    if (!feof(stdin)) refuse("unreadable input");
    return 0;
}
