/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The emitted journal scanner against `dn-compiler journal-model`: each line of standard input is a
 * journal in hexadecimal, `-` for none, the most octets one read adds to the window, and what the
 * model reads in it. Stepped as a caller does, a frame a step, the scanner has to read the same; its
 * area ends at a page without access, and it may ask only for octets the journal has, that fit the
 * window, and point only into the window. */
#define _GNU_SOURCE
#include "cake_runtime.h"
#include "dn_scan_layout.h"
#include "host.h"
#include <inttypes.h>
extern uint32_t dn_scan_step(uint64_t area);

static char *said;
static size_t said_len, said_cap;

static void say(const char *text, size_t n) {
    if (said_len + n + 1 > said_cap) {
        said_cap = 2 * (said_len + n + 1);
        said = realloc(said, said_cap);
        if (!said) dn_harness("out of memory");
    }
    memcpy(said + said_len, text, n);
    said_len += n;
    said[said_len] = 0;
}

static void sayf(const char *format, ...) __attribute__((format(printf, 1, 2)));
static void sayf(const char *format, ...) {
    char text[64];
    va_list args;
    va_start(args, format);
    int n = vsnprintf(text, sizeof text, format, args);
    va_end(args);
    say(text, (size_t)n);
}

static void say_hex(const unsigned char *p, uint64_t n) {
    static const char digits[] = "0123456789abcdef";
    for (uint64_t i = 0; i < n; ++i) say((char[]){digits[p[i] >> 4], digits[p[i] & 15]}, 2);
}

/* Where an octet the scanner points to lies: in the window's octets, `n` of them. */
static const unsigned char *in_window(const unsigned char *a, uint64_t at, uint64_t n) {
    uint64_t from = (uintptr_t)(a + DN_SCAN_WINDOW), len = dn_word(a + DN_SCAN_LEN);
    if (at < from || n > len || at - from > len - n) dn_violation("a record points outside the window");
    return (const unsigned char *)(uintptr_t)at;
}

static void record(const unsigned char *a) {
    switch (dn_word(a + DN_SCAN_TYPE)) {
    case 1:
        say("F:", 2);
        say_hex(a + DN_SCAN_KEY, 16);
        break;
    case 2: {
        sayf("C:%" PRIu64 ":", dn_word(a + DN_SCAN_SEQ));
        uint64_t id_len = dn_word(a + DN_SCAN_ID_LEN), groups = dn_word(a + DN_SCAN_GROUP_COUNT);
        say_hex(in_window(a, dn_word(a + DN_SCAN_ID_AT), id_len), id_len);
        sayf(":%" PRIu64 ":%" PRIu64 ":%" PRIu64 ":", dn_word(a + DN_SCAN_HEADER), dn_word(a + DN_SCAN_FILE_SIZE),
             dn_word(a + DN_SCAN_CRC));
        if (groups > 16) dn_violation("a commit of %" PRIu64 " groups", groups);
        for (uint64_t g = 0; g < groups; ++g) {
            const unsigned char *slot = a + DN_SCAN_GROUPS + g * DN_SCAN_GROUP_SLOT;
            uint64_t len = dn_word(slot + 8);
            if (g) say(",", 1);
            say_hex(in_window(a, dn_word(slot), len), len);
            sayf("=%" PRIu64, dn_word(slot + 16));
        }
        break;
    }
    case 3:
        say("S", 1);
        break;
    default:
        dn_violation("a record of type %" PRIu64, dn_word(a + DN_SCAN_TYPE));
    }
    say(" ", 1);
}

/* The journal `j` read by the scanner, `chunk` octets a read at most; how many records it read. */
static uint64_t scan(const unsigned char *j, size_t n, uint64_t chunk) {
    static const char *const why[] = {"", "short", "too-long", "unterminated", "tag", "not-a-record",
                                      "format-again"};
    struct dn_span g = dn_before_guard(DN_SCAN_AREA);
    unsigned char *a = g.data;
    memset(a, 0x5a, DN_SCAN_AREA);
    dn_put_word(a + DN_SCAN_SIZE, n);
    for (int w = DN_SCAN_BASE; w <= DN_SCAN_COUNT; w += 8) dn_put_word(a + w, 0);
    said_len = 0;
    uint64_t records = 0;
    for (uint64_t steps = 0;; ++steps) {
        if (steps > 2 * n + 16) dn_violation("the scanner took %" PRIu64 " steps over %zu octets", steps, n);
        uint32_t status = dn_scan_step((uintptr_t)a);
        if (status != dn_word(a + DN_SCAN_STATUS)) dn_violation("the scanner returned another status");
        uint64_t base = dn_word(a + DN_SCAN_BASE), len = dn_word(a + DN_SCAN_LEN), pos = dn_word(a + DN_SCAN_POS);
        if (status == DN_SCAN_WANTED) {
            uint64_t want = dn_word(a + DN_SCAN_WANT), take = want < chunk ? want : chunk;
            if (!want || len > DN_SCAN_WINDOW_MAX - want || base > n || len > n - base || want > n - base - len)
                dn_violation("the scanner asked for %" PRIu64 " octets after %" PRIu64 " in its window from %" PRIu64,
                             want, len, base);
            memcpy(a + DN_SCAN_WINDOW + len, j + base + len, take);
            dn_put_word(a + DN_SCAN_LEN, len + take);
        } else if (status == DN_SCAN_RECORD) {
            record(a);
            ++records;
        } else {
            say("end ", 4);
            if (status == DN_SCAN_CLEAN) say("clean", 5);
            else if (status == DN_SCAN_TORN) sayf("torn %" PRIu64, pos);
            else if (status == DN_SCAN_CORRUPT && dn_word(a + DN_SCAN_WHY) - 1 < 6)
                sayf("corrupt %" PRIu64 " %s", pos, why[dn_word(a + DN_SCAN_WHY)]);
            else dn_violation("the scanner stopped with status %" PRIu32, status);
            break;
        }
    }
    dn_unmap(g);
    return records;
}

int main(void) {
    dn_expect_faults();
    dn_runtime_init();
    static char line[1 << 24];
    static unsigned char journal[1 << 23];
    uint64_t cases = 0, records = 0;
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\n")] = 0;
        char *chunk = strchr(line, ' '), *want = chunk ? strchr(chunk + 1, ' ') : NULL;
        if (!want) dn_harness("a line without its chunk and answer");
        *chunk++ = 0;
        *want++ = 0;
        size_t n = strcmp(line, "-") ? strlen(line) / 2 : 0;
        if ((n && strlen(line) % 2) || n > sizeof journal) dn_harness("a journal of odd or excessive length");
        for (size_t i = 0; i < n; ++i) {
            unsigned v;
            if (sscanf(line + 2 * i, "%2x", &v) != 1) dn_harness("a journal not in hexadecimal");
            journal[i] = (unsigned char)v;
        }
        uint64_t most = dn_parse_u64(chunk, DN_SCAN_WINDOW_MAX);
        if (!most) dn_harness("reads of no octets");
        records += scan(journal, n, most);
        if (strcmp(said, want)) dn_violation("scan of %zu octets read %.300s, not %.300s", n, said, want);
        ++cases;
    }
    printf("{\"scan_cases\": %" PRIu64 ", \"scan_records\": %" PRIu64 "}\n", cases, records);
    return 0;
}
