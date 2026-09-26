/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The emitted reply table against the replies the Lean program computes. Each case is read
 * from stdin as the input and the expected reply in hex ("-" when empty); the argument is the
 * buffer the program asks for. The input and the output buffer sit against a page without
 * access, once after them and once before them, and the input is read-only during the call. */
#define _GNU_SOURCE
#include "cake_runtime.h"
#include <inttypes.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
extern uint32_t dn_reply(uint64_t, uint64_t, uint64_t, uint64_t);

enum { LIMIT = 4096 };
static size_t page_size;

static void protect(unsigned char *page, int access) {
    if (mprotect(page, page_size, access)) {
        perror("mprotect");
        exit(1);
    }
}

/* The middle one of three pages; the outer two have no access. */
static unsigned char *guarded(void) {
    unsigned char *pages = mmap(NULL, page_size * 3, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (pages == MAP_FAILED) return NULL;
    protect(pages + page_size, PROT_READ | PROT_WRITE);
    return pages + page_size;
}

static int nibble(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

static int unhex(const char *text, unsigned char *bytes, size_t *len) {
    if (strcmp(text, "-") == 0) { *len = 0; return 0; }
    size_t digits = strlen(text);
    if (digits == 0 || digits % 2 || digits / 2 > LIMIT) return 1;
    for (size_t i = 0; i < digits / 2; ++i) {
        int high = nibble(text[2 * i]), low = nibble(text[2 * i + 1]);
        if (high < 0 || low < 0) return 1;
        bytes[i] = (unsigned char)(high * 16 + low);
    }
    *len = digits / 2;
    return 0;
}

/* Every byte of the page is `fill`, except `len` bytes at `from`, which are `bytes`. */
static int page_holds(const unsigned char *page, unsigned char fill, const unsigned char *from,
                      const unsigned char *bytes, size_t len) {
    for (size_t i = 0; i < page_size; ++i) {
        const unsigned char *at = page + i;
        unsigned char want = at >= from && at < from + len ? bytes[at - from] : fill;
        if (*at != want) return 0;
    }
    return 1;
}

/* One call, with both buffers at the end of their page or at its start. A refused call
   returns UINT32_MAX and writes nothing; any other returns the reply's length with the reply
   at `out` and nothing else written. The fill changes with the placement, so a write of the
   value already there shows in the other one. */
static int call(unsigned char *in_page, const unsigned char *input, uint64_t in_len,
                unsigned char *out_page, uint64_t cap, const unsigned char *expected,
                size_t expected_len, int refused, int at_start) {
    size_t placed = in_len <= LIMIT ? (size_t)in_len : 0;
    size_t room = cap <= LIMIT ? (size_t)cap : 0;
    unsigned char in_fill = at_start ? 0xa5 : 0x5a, out_fill = at_start ? 0x5a : 0xa5;
    memset(in_page, in_fill, page_size);
    unsigned char *in = at_start ? in_page : in_page + page_size - placed;
    memcpy(in, input, placed);
    memset(out_page, out_fill, page_size);
    unsigned char *out = at_start ? out_page : out_page + page_size - room;
    protect(in_page, PROT_READ);
    uint32_t got = dn_reply((uintptr_t)in, in_len, (uintptr_t)out, cap);
    protect(in_page, PROT_READ | PROT_WRITE);
    if (!page_holds(in_page, in_fill, in, input, placed)) return 0;
    if (refused) return got == UINT32_MAX && page_holds(out_page, out_fill, out, expected, 0);
    return got == expected_len && page_holds(out_page, out_fill, out, expected, expected_len);
}

int main(int argc, char **argv) {
    if (argc != 2 || argv[1][0] < '0' || argv[1][0] > '9') return 2;
    char *end;
    unsigned long max_len = strtoul(argv[1], &end, 10);
    if (*end || max_len == 0 || max_len > LIMIT - 9) return 2;
    dn_runtime_init();
    page_size = (size_t)sysconf(_SC_PAGESIZE);
    unsigned char *in_page = guarded(), *out_page = guarded();
    if (!in_page || !out_page) return 1;
    /* One byte wider than the longest token, so a longer one is refused rather than split. */
    static char in_text[2 * LIMIT + 2], out_text[2 * LIMIT + 2];
    static unsigned char input[LIMIT], expected[LIMIT];
    uint64_t cases = 0;
    int read;
    while ((read = scanf("%8193s %8193s", in_text, out_text)) == 2) {
        size_t in_len, expected_len;
        if (unhex(in_text, input, &in_len) || unhex(out_text, expected, &expected_len) ||
            expected_len > max_len)
            return 2;
        /* A buffer of exactly what the program asks for, a larger one, one byte too small, and
           the two lengths a signed comparison reads as negative. A negative capacity is also
           below the program's own bound, so no call tells its separate check from that one. */
        struct { uint64_t in_len, cap; int refused; } calls[] = {
            {in_len, max_len, 0}, {in_len, max_len + 9, 0}, {in_len, max_len - 1, 1},
            {UINT64_MAX, max_len, 1}, {in_len, UINT64_C(1) << 63, 1}};
        for (size_t c = 0; c < sizeof(calls) / sizeof(calls[0]); ++c)
            for (int at_start = 0; at_start < 2; ++at_start) {
                if (!call(in_page, input, calls[c].in_len, out_page, calls[c].cap, expected,
                          expected_len, calls[c].refused, at_start)) {
                    fprintf(stderr, "reply mismatch for input %s, length %" PRIu64 ", room %"
                            PRIu64 ", at the %s of the page\n", in_text, calls[c].in_len,
                            calls[c].cap, at_start ? "start" : "end");
                    return 1;
                }
                ++cases;
            }
    }
    if (read != EOF || cases == 0) return 2;
    munmap(in_page - page_size, page_size * 3);
    munmap(out_page - page_size, page_size * 3);
    printf("{\"reply_cases\":%" PRIu64 "}\n", cases);
    return 0;
}
