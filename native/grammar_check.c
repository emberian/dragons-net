/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The grammar's functions (DN.News.AbnfProg) as the grammar lane runs them: each line of standard
 * input is a rule's number, an input in hexadecimal, `-` for none, and the positions its matches
 * start from, comma-separated, 0 if none are given. The program's answer to each is printed, a line
 * each: 1 if a match from one of them ends at the input's end, 0 if not. With `--time`
 * each answer is followed by the microseconds the program took. Before the run the heap outside
 * the area is filled; on every call it has to be as filled, the header the compiler theorem
 * requires intact, and the arrays the area. */
#define _GNU_SOURCE
#include "call_checks.h"
#include "dn_grammar_layout.h"
#include <time.h>

_Static_assert(DN_GRAMMAR_AT + DN_GRAMMAR_AREA <= DN_RUNTIME_SEGMENT_BYTES, "the area does not fit the heap");

#define FILL UINT64_C(0x5A5A5A5A5A5A5A5A)

static int asked, timed;
static struct timespec started;
static char *line;
static size_t line_cap;

static int in_area(size_t offset) { return offset >= DN_GRAMMAR_AT && offset < DN_GRAMMAR_AT + DN_GRAMMAR_AREA; }

static void fill_heap(void) {
    for (size_t offset = DN_HEADER_BYTES; offset < DN_RUNTIME_SEGMENT_BYTES; offset += 8)
        if (!in_area(offset)) dn_put_word(dn_heap_at(offset), FILL);
}

static void fill_checked(const char *call) {
    for (size_t offset = DN_HEADER_BYTES; offset < DN_RUNTIME_SEGMENT_BYTES; offset += 8)
        if (!in_area(offset) && dn_word(dn_heap_at(offset)) != FILL)
            dn_violation("%s: the program wrote outside its area, at heap offset %zu", call, offset);
}

static long micros(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (now.tv_sec - started.tv_sec) * 1000000L + (now.tv_nsec - started.tv_nsec) / 1000;
}

static int hex_digit(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    dn_harness("not a hexadecimal digit: %c", c);
}

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen) {
    long took = micros();
    dn_header_checked("dn_next");
    if (c != dn_heap_at(DN_GRAMMAR_AT) || clen != 8 || a != dn_heap_at(DN_GRAMMAR_AT) || alen != DN_GRAMMAR_AREA)
        dn_violation("dn_next: the arrays are not the area");
    fill_checked("dn_next");
    if (asked) {
        uint64_t answer = dn_word(a + DN_GRAMMAR_ANSWER);
        if (answer > 1) dn_violation("dn_next: the answer %" PRIu64 " to a case in range", answer);
        if (timed) printf("%" PRIu64 " %ld\n", answer, took);
        else printf("%" PRIu64 "\n", answer);
    }
    ssize_t got = getline(&line, &line_cap, stdin);
    if (got < 0) {
        if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
        exit(0);
    }
    if (got > 0 && line[got - 1] == '\n') line[--got] = 0;
    char *space = strchr(line, ' ');
    if (!space) dn_harness("not a rule and an input: %s", line);
    *space = 0;
    uint64_t rule = dn_parse_u64(line, DN_GRAMMAR_RULES - 1);
    char *hex = space + 1, *starts = strchr(hex, ' ');
    if (starts) *starts++ = 0;
    size_t digits = strlen(hex), len = 0;
    if (strcmp(hex, "-") != 0) {
        if (digits % 2 || digits / 2 > DN_GRAMMAR_INPUT_MAX) dn_harness("not an input of at most %d octets", DN_GRAMMAR_INPUT_MAX);
        len = digits / 2;
        for (size_t i = 0; i < len; ++i)
            a[DN_GRAMMAR_INPUT + i] = (unsigned char)(hex_digit(hex[2 * i]) * 16 + hex_digit(hex[2 * i + 1]));
    }
    uint64_t count = 0;
    if (!starts) {
        dn_put_word(a + DN_GRAMMAR_START_LIST, 0);
        count = 1;
    } else {
        for (char *start = strtok(starts, ","); start; start = strtok(NULL, ",")) {
            if (count == DN_GRAMMAR_STARTS_MAX) dn_harness("more than %d starts", DN_GRAMMAR_STARTS_MAX);
            dn_put_word(a + DN_GRAMMAR_START_LIST + 8 * count++, dn_parse_u64(start, len));
        }
    }
    dn_put_word(a + DN_GRAMMAR_STARTS, count);
    dn_put_word(a + DN_GRAMMAR_RULE, rule);
    dn_put_word(a + DN_GRAMMAR_LEN, len);
    asked = 1;
    clock_gettime(CLOCK_MONOTONIC, &started);
}

void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen) {
    (void)c, (void)clen, (void)a, (void)alen;
    dn_violation("dn_emit: the grammar's program has no such call");
}

static void on_exit_run(int code) { dn_violation("the run ended for want of stack or heap (code %d)", code); }

int main(int argc, char **argv) {
    timed = argc == 2 && strcmp(argv[1], "--time") == 0;
    if (argc > 2 || (argc == 2 && !timed)) dn_harness("usage: grammar-check [--time]");
    dn_runtime_setup();
    dn_runtime_header();
    fill_heap();
    dn_runtime_on_exit = on_exit_run;
    cml_main();
    dn_violation("the program returned to its host, which a build without --main_return cannot do");
}
