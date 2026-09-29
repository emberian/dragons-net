/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Host for the framers (scripts/framing_check.py). Each line of stdin is one case, as
 * `dn-compiler frame-model` reads it:
 *
 *   L LIM CHUNK...      command lines of at most LIM octets (512 or 4)
 *   B CAP CHUNK...      a block for a buffer of CAP bytes (64 or 4)
 *
 * with each chunk in hex, `-` for an empty one. The host feeds the chunks to the compiled framer a
 * chunk at a time, calling again from where the last call stopped until the chunk is read; after a
 * block ends, the next one starts from the state it left. It answers each case with one line in the
 * model's form. A call that reports nothing has to read the whole chunk, and one that reports a line
 * or a block has to stop after it.
 *
 * Each chunk ends where its page ends, before a page without access, and the page is read-only
 * while the framer runs: a read past the chunk or a write into it ends the process. The framer's
 * state ends as near to its page's end as its alignment allows, so a write past a block of 512 or
 * 64 bytes ends the process as well; the rest of the state's page is filled, and after every call
 * it has to be as it was, which catches a write anywhere else outside the block.
 *
 * Before the cases, each framer is called with a negative count, a negative position and a position
 * past the count, which it has to refuse without reading its input or touching its state. */
#include "cake_runtime.h"
#include "host.h"
#include <inttypes.h>

typedef uint32_t framer(uint64_t blk, uint64_t p, uint64_t n, uint64_t i);
framer dn_frame_line, dn_frame_line_4, dn_frame_block_64, dn_frame_block_4;

enum { STATE_WORDS = 40, MAX_CHUNKS = 4096, MAX_CASE = 1 << 20, FILL = 0xa5 };
static const uint32_t REFUSED = UINT32_MAX;

static const char *kinds[] = {"none", "command", "malformed", "overlong"};
static const char *verdicts[] = {"none", "accepted", "refused", "too-large"};
static const char *phases[] = {"bol", "data", "cr", "dot", "dotcr"};

static unsigned char *chunk_page, *state_page, *nowhere, *block_start;
static size_t block_bytes;
static char line[MAX_CASE];

static void hex(const unsigned char *bytes, uint64_t count) {
    if (count == 0) {
        putchar('-');
        return;
    }
    for (uint64_t k = 0; k < count; ++k) printf("%02x", bytes[k]);
}

static int digit(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    dn_harness("bad input: not hex: %c", c);
}

/* The chunk in `text`, laid so that its last byte is the last of its page, which is left
   read-only. */
static unsigned char *chunk(const char *text, uint64_t *count) {
    size_t length = strlen(text), page = dn_page_size();
    if (strcmp(text, "-") == 0) length = 0;
    if (length % 2 || length / 2 > page) dn_harness("bad input: a chunk of %zu hex digits", length);
    *count = length / 2;
    dn_protect(chunk_page, PROT_READ | PROT_WRITE);
    unsigned char *at = chunk_page + page - *count;
    for (uint64_t k = 0; k < *count; ++k) at[k] = (unsigned char)(digit(text[2 * k]) * 16 + digit(text[2 * k + 1]));
    dn_protect(chunk_page, PROT_READ);
    return at;
}

/* A fresh state for a framer keeping `room` bytes: zero words, laid at the end of its page. */
static unsigned char *fresh(uint64_t room) {
    size_t page = dn_page_size(), size = (STATE_WORDS + room + 7) / 8 * 8;
    unsigned char *blk = state_page + page - size;
    memset(state_page, FILL, page);
    memset(blk, 0, STATE_WORDS);
    block_start = blk;
    block_bytes = STATE_WORDS + room;
    return blk;
}

/* The state's page outside the block is as `fresh` left it. */
static void outside_untouched(void) {
    size_t page = dn_page_size();
    for (unsigned char *q = state_page; q < state_page + page; ++q)
        if ((q < block_start || q >= block_start + block_bytes) && *q != FILL)
            dn_violation("the framer wrote outside its block, at offset %td from it", q - block_start);
}

/* One call from `i`: where it stopped, which has to be past `i` and within the chunk, and at its
   end when it reports nothing; at the end of a line or a block when it does. */
static uint32_t call(framer *f, unsigned char *blk, const unsigned char *p, uint64_t n, uint64_t i) {
    uint32_t next = f((uint64_t)(uintptr_t)blk, (uint64_t)(uintptr_t)p, n, i);
    outside_untouched();
    if (next <= i || next > n) dn_violation("a call from %" PRIu64 " of %" PRIu64 " returned %" PRIu32, i, n, next);
    uint64_t kind = dn_word(blk + 24);
    if (kind == 0 && next != n)
        dn_violation("a call from %" PRIu64 " of %" PRIu64 " stopped at %" PRIu32 " with nothing to report", i, n,
                     next);
    if (kind != 0 && p[next - 1] != '\n')
        dn_violation("a call from %" PRIu64 " of %" PRIu64 " reported at %" PRIu32 ", not after an LF", i, n, next);
    return next;
}

/* Calls the framer has to refuse: with the input on a page without access and the whole of the
   state's page filled, it returns the refusal and the page is as it was. */
static void refusals(framer *f, uint64_t room) {
    static const uint64_t calls[][2] = {{1, 2}, {UINT64_MAX, 0}, {1, UINT64_MAX}, {UINT64_C(1) << 63, 0}};
    size_t page = dn_page_size();
    unsigned char *blk = fresh(room);
    memset(state_page, FILL, page);
    for (size_t k = 0; k < sizeof calls / sizeof calls[0]; ++k) {
        uint64_t n = calls[k][0], i = calls[k][1];
        uint32_t next = f((uint64_t)(uintptr_t)blk, (uint64_t)(uintptr_t)nowhere, n, i);
        if (next != REFUSED)
            dn_violation("a call from %" PRIu64 " of %" PRIu64 " was not refused: it returned %" PRIu32, i, n, next);
        for (unsigned char *q = state_page; q < state_page + page; ++q)
            if (*q != FILL) dn_violation("a refused call wrote at offset %td from its block", q - blk);
    }
}

static void lines(uint64_t lim, char **chunks, size_t count) {
    framer *f = lim == 512 ? dn_frame_line : dn_frame_line_4;
    unsigned char *blk = fresh(lim);
    printf("L lines");
    for (size_t c = 0; c < count; ++c) {
        uint64_t n;
        const unsigned char *p = chunk(chunks[c], &n);
        for (uint64_t i = 0; i < n;) {
            i = call(f, blk, p, n, i);
            uint64_t kind = dn_word(blk + 24);
            if (kind > 3) dn_violation("a line of kind %" PRIu64, kind);
            if (kind) {
                uint64_t kept = dn_word(blk + 32);
                if (kept > lim) dn_violation("a line keeps %" PRIu64 " bytes", kept);
                printf(" %s:", kinds[kind]);
                hex(blk + STATE_WORDS, kept);
            }
        }
    }
    uint64_t len = dn_word(blk), cr = dn_word(blk + 8), bad = dn_word(blk + 16);
    if (len > lim || cr > 1 || bad > 1)
        dn_violation("a state out of range: %" PRIu64 " %" PRIu64 " %" PRIu64, len, cr, bad);
    printf(" state %" PRIu64 " %" PRIu64 " %" PRIu64 " ", len, cr, bad);
    hex(blk + STATE_WORDS, len);
    putchar('\n');
}

static void blocks(uint64_t cap, char **chunks, size_t count) {
    framer *f = cap == 64 ? dn_frame_block_64 : dn_frame_block_4;
    unsigned char *blk = fresh(cap);
    uint64_t read = 0;
    printf("B");
    for (size_t c = 0; c < count; ++c) {
        uint64_t n;
        const unsigned char *p = chunk(chunks[c], &n);
        for (uint64_t i = 0; i < n;) {
            uint64_t from = i;
            i = call(f, blk, p, n, i);
            read += i - from;
            uint64_t kind = dn_word(blk + 24);
            if (kind > 3) dn_violation("a block of kind %" PRIu64, kind);
            if (kind) {
                uint64_t held = dn_word(blk + 32);
                if (held > cap) dn_violation("a block holds %" PRIu64 " bytes", held);
                printf(" end %s:", verdicts[kind]);
                hex(blk + STATE_WORDS, held);
                printf(" %" PRIu64, read);
                read = 0;
            }
        }
    }
    uint64_t phase = dn_word(blk), bad = dn_word(blk + 8), size = dn_word(blk + 16);
    if (phase > 4 || bad > 1 || size > cap + 1)
        dn_violation("a block state out of range: %" PRIu64 " %" PRIu64 " %" PRIu64, phase, bad, size);
    printf(" open %s %" PRIu64 " %" PRIu64 " ", phases[phase], bad, size);
    hex(blk + STATE_WORDS, size < cap ? size : cap);
    putchar('\n');
}

int main(void) {
    dn_expect_faults();
    dn_runtime_init();
    chunk_page = dn_guarded();
    state_page = dn_guarded();
    nowhere = dn_inaccessible();
    refusals(dn_frame_line, 512);
    refusals(dn_frame_line_4, 4);
    refusals(dn_frame_block_64, 64);
    refusals(dn_frame_block_4, 4);
    static char *chunks[MAX_CHUNKS];
    while (fgets(line, sizeof line, stdin)) {
        size_t length = strlen(line);
        if (length && line[length - 1] == '\n') line[--length] = 0;
        else if (!feof(stdin)) dn_harness("bad input: a case of %d characters or more", MAX_CASE - 1);
        char *mode = strtok(line, " "), *size = strtok(NULL, " ");
        if (!mode || !size) dn_harness("bad input: a case without its mode and size");
        size_t count = 0;
        for (char *text; (text = strtok(NULL, " "));) {
            if (count == MAX_CHUNKS) dn_harness("bad input: more than %d chunks", MAX_CHUNKS);
            chunks[count++] = text;
        }
        uint64_t n = dn_parse_u64(size, 512);
        if (strcmp(mode, "L") == 0 && (n == 512 || n == 4)) lines(n, chunks, count);
        else if (strcmp(mode, "B") == 0 && (n == 64 || n == 4)) blocks(n, chunks, count);
        else dn_harness("bad input: no framer for %s %s", mode, size);
        if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
    }
    if (!feof(stdin)) dn_harness("bad input: unreadable");
    return 0;
}
