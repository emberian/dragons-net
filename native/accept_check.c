/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The article's check (DN.News.ArticleProg) as the article lane runs it: each line of standard input
 * is a case as `dn-compiler article-model` reads one, and the program's answer to it is printed as
 * the model prints its own. A case's context goes to the program when it changes; a context or a
 * wall clock the program refuses ends the run with status 3, as a context the model refuses ends
 * its run. An article
 * goes up to the end of its first empty line, as the session gathers a header section. With
 * `--time` each answer is followed by the microseconds the program took. Before the run the heap
 * outside the area is filled; on every call it has to be as filled, the header the compiler theorem
 * requires intact, and the arrays the area. */
#define _GNU_SOURCE
#include "call_checks.h"
#include "dn_article_layout.h"
#include <time.h>

_Static_assert(DN_ARTICLE_AT + DN_ARTICLE_AREA <= DN_RUNTIME_SEGMENT_BYTES, "the area does not fit the heap");

#define FILL UINT64_C(0x5A5A5A5A5A5A5A5A)

enum { MODE_CHECK = 0, MODE_FORMAT = 1, MODE_PARSE = 2, MODE_CONTEXT = 3, OUT_OF_RANGE = 255 };

static const char *reasons[DN_ARTICLE_REFUSALS] = {DN_ARTICLE_REASONS};
static int timed, pending = -1, context_known;
static struct timespec started;
static char *line, *context;
static size_t line_cap;
static unsigned char *article;
static size_t article_len;

static unsigned char *area(void) { return dn_heap_at(DN_ARTICLE_AT); }
/* The heap outside the area: past the header to the area, and past the area to the end. */
static const size_t outside[2][2] = {{DN_HEADER_BYTES, DN_ARTICLE_AT},
                                     {DN_ARTICLE_AT + DN_ARTICLE_AREA, DN_RUNTIME_SEGMENT_BYTES}};

static void fill_heap(void) {
    for (int k = 0; k < 2; ++k)
        for (size_t offset = outside[k][0]; offset < outside[k][1]; offset += 8) dn_put_word(dn_heap_at(offset), FILL);
}

static void fill_checked(void) {
    for (int k = 0; k < 2; ++k)
        for (size_t offset = outside[k][0]; offset < outside[k][1]; offset += 8)
            if (dn_word(dn_heap_at(offset)) != FILL)
                dn_violation("dn_next: the program wrote outside its area, at heap offset %zu", offset);
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

/* The bytes `hex` writes, `-` for none, into `out`, at most `cap` of them; their number. */
static size_t unhex(const char *hex, unsigned char *out, size_t cap, const char *what) {
    if (strcmp(hex, "-") == 0) return 0;
    size_t digits = strlen(hex);
    if (digits % 2 || digits / 2 > cap) dn_harness("%s: not hex of at most %zu octets", what, cap);
    for (size_t i = 0; i < digits / 2; ++i)
        out[i] = (unsigned char)(hex_digit(hex[2 * i]) * 16 + hex_digit(hex[2 * i + 1]));
    return digits / 2;
}

static void print_hex(const unsigned char *bytes, uint64_t len) {
    if (!len) fputc('-', stdout);
    for (uint64_t i = 0; i < len; ++i) printf("%02x", bytes[i]);
}

static char *field(char **rest) {
    char *word = strsep(rest, " ");
    if (!word) dn_harness("a case with too few fields: %s", line);
    return word;
}

/* The context of a check: the numbers, the identity, the random value and the groups, into the area. */
static void put_context(char *seq, char *run, char *conn, char *identity, char *random, char *groups) {
    unsigned char *a = area();
    dn_put_word(a + DN_ARTICLE_SEQ, dn_parse_u64(seq, UINT64_MAX));
    dn_put_word(a + DN_ARTICLE_RUN, dn_parse_u64(run, UINT64_MAX));
    dn_put_word(a + DN_ARTICLE_CONN, dn_parse_u64(conn, UINT64_MAX));
    dn_put_word(a + DN_ARTICLE_ID_LEN, unhex(identity, a + DN_ARTICLE_ID, DN_ARTICLE_ID_CAP, "the identity"));
    dn_put_word(a + DN_ARTICLE_RAND_LEN, unhex(random, a + DN_ARTICLE_RAND, DN_ARTICLE_RAND_CAP, "the random value"));
    uint64_t count = 0;
    if (strcmp(groups, "-") != 0) {
        for (char *group; (group = strsep(&groups, ","));) {
            if (count == DN_ARTICLE_GROUPS_CAP) dn_harness("more than %d groups", DN_ARTICLE_GROUPS_CAP);
            unsigned char *at = a + DN_ARTICLE_GROUPS + DN_ARTICLE_GROUP_SIZE * count++;
            dn_put_word(at, unhex(group, at + 8, DN_ARTICLE_GROUP_SIZE - 8, "a group"));
        }
    }
    dn_put_word(a + DN_ARTICLE_GROUPS_N, count);
}

/* The article up to the end of its first empty line, or all of it if it has none. */
static void put_article(void) {
    size_t len = article_len;
    if (len >= 2 && article[0] == '\r' && article[1] == '\n') len = 2;
    else
        for (size_t i = 0; i + 4 <= article_len; ++i)
            if (memcmp(article + i, "\r\n\r\n", 4) == 0) {
                len = i + 4;
                break;
            }
    if (len > DN_ARTICLE_INPUT_MAX) dn_harness("an article with no empty line in its first %d octets", DN_ARTICLE_INPUT_MAX);
    memcpy(area() + DN_ARTICLE_INPUT, article, len);
    dn_put_word(area() + DN_ARTICLE_LEN, len);
    dn_put_word(area() + DN_ARTICLE_MODE, MODE_CHECK);
    pending = MODE_CHECK;
}

static void answer_check(const unsigned char *a, uint64_t verdict) {
    if (verdict == 0) {
        fputs("accepted ", stdout);
        uint64_t out = dn_word(a + DN_ARTICLE_OUT_LEN), msg = dn_word(a + DN_ARTICLE_MSG_LEN);
        uint64_t known = dn_word(a + DN_ARTICLE_KNOWN_N), groups = dn_word(a + DN_ARTICLE_GROUPS_N);
        if (out > DN_ARTICLE_OUT_MAX || msg > DN_ARTICLE_MSG_CAP || known > DN_ARTICLE_KNOWN_MAX)
            dn_violation("dn_next: an accepted article's lengths past their bounds");
        print_hex(a + DN_ARTICLE_OUT, out);
        fputc(' ', stdout);
        print_hex(a + DN_ARTICLE_MSG, msg);
        fputc(' ', stdout);
        if (!known) fputc('-', stdout);
        for (uint64_t k = 0; k < known; ++k) {
            uint64_t g = dn_word(a + DN_ARTICLE_KNOWN + 8 * k);
            if (g >= groups) dn_violation("dn_next: group %" PRIu64 " of %" PRIu64, g, groups);
            const unsigned char *at = a + DN_ARTICLE_GROUPS + DN_ARTICLE_GROUP_SIZE * g;
            if (k) fputc(',', stdout);
            print_hex(at + 8, dn_word(at));
        }
    } else {
        if (verdict > DN_ARTICLE_REFUSALS) dn_violation("dn_next: the verdict %" PRIu64, verdict);
        uint64_t len = dn_word(a + DN_ARTICLE_NAME_LEN);
        if (len > DN_ARTICLE_NAME_CAP) dn_violation("dn_next: a name of %" PRIu64 " octets", len);
        printf("refused %s ", reasons[verdict - 1]);
        print_hex(a + DN_ARTICLE_NAME, len);
    }
}

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen) {
    long took = micros();
    dn_header_checked("dn_next");
    if (c != area() || clen != 8 || a != area() || alen != DN_ARTICLE_AREA)
        dn_violation("dn_next: the arrays are not the area");
    fill_checked();
    if (pending >= 0) {
        uint64_t verdict = dn_word(a + DN_ARTICLE_VERDICT);
        if (verdict == OUT_OF_RANGE && pending != MODE_PARSE && dn_word(a + DN_ARTICLE_WALL) >= DN_ARTICLE_WALL_MAX) {
            fflush(stdout);
            fprintf(stderr, "the program refuses the wall clock %" PRIu64 "\n", dn_word(a + DN_ARTICLE_WALL));
            exit(3);
        }
        if (verdict == OUT_OF_RANGE) dn_violation("dn_next: a request in range answered as out of range");
        if (pending == MODE_CONTEXT) {
            if (verdict > 1) dn_violation("dn_next: the context answered %" PRIu64, verdict);
            if (!verdict) {
                fflush(stdout);
                fprintf(stderr, "the program refuses the context: %s\n", context);
                exit(3);
            }
            context_known = 1;
            put_article();
            clock_gettime(CLOCK_MONOTONIC, &started);
            return;
        }
        if (pending == MODE_CHECK) answer_check(a, verdict);
        else if (pending == MODE_FORMAT) {
            if (verdict) dn_violation("dn_next: the date answered %" PRIu64, verdict);
            uint64_t len = dn_word(a + DN_ARTICLE_OUT_LEN);
            if (len > DN_ARTICLE_OUT_MAX) dn_violation("dn_next: a date of %" PRIu64 " octets", len);
            print_hex(a + DN_ARTICLE_OUT, len);
        } else if (verdict == 0) printf("%" PRId64, (int64_t)dn_word(a + DN_ARTICLE_VALUE));
        else if (verdict == 1) fputc('-', stdout);
        else dn_violation("dn_next: the reading answered %" PRIu64, verdict);
        if (timed) printf(" %ld", took);
        fputc('\n', stdout);
    }
    ssize_t got = getline(&line, &line_cap, stdin);
    if (got < 0) {
        if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
        exit(0);
    }
    if (got > 0 && line[got - 1] == '\n') line[--got] = 0;
    char *rest = line, *kind = field(&rest);
    if (strcmp(kind, "check") == 0) {
        char *wall = field(&rest), *seq = field(&rest), *run = field(&rest), *conn = field(&rest);
        char *identity = field(&rest), *random = field(&rest), *groups = field(&rest), *hex = field(&rest);
        if (rest) dn_harness("a case with too many fields: %s", line);
        dn_put_word(a + DN_ARTICLE_WALL, dn_parse_u64(wall, UINT64_MAX));
        free(article);
        article = malloc(strlen(hex) / 2 + 1);
        if (!article) dn_harness("malloc: %s", strerror(errno));
        article_len = unhex(hex, article, strlen(hex) / 2, "the article");
        char *same = NULL;
        if (asprintf(&same, "%s %s %s %s %s %s", seq, run, conn, identity, random, groups) < 0)
            dn_harness("asprintf: %s", strerror(errno));
        if (context_known && strcmp(same, context) == 0) {
            free(same);
            put_article();
        } else {
            free(context);
            context = same;
            context_known = 0;
            put_context(seq, run, conn, identity, random, groups);
            dn_put_word(a + DN_ARTICLE_MODE, MODE_CONTEXT);
            pending = MODE_CONTEXT;
        }
    } else if (strcmp(kind, "format") == 0) {
        dn_put_word(a + DN_ARTICLE_WALL, dn_parse_u64(field(&rest), UINT64_MAX));
        if (rest) dn_harness("a case with too many fields: %s", line);
        dn_put_word(a + DN_ARTICLE_MODE, MODE_FORMAT);
        pending = MODE_FORMAT;
    } else if (strcmp(kind, "parse") == 0) {
        char *hex = field(&rest);
        if (rest) dn_harness("a case with too many fields: %s", line);
        dn_put_word(a + DN_ARTICLE_LEN, unhex(hex, a + DN_ARTICLE_INPUT, DN_ARTICLE_INPUT_MAX, "a date"));
        dn_put_word(a + DN_ARTICLE_MODE, MODE_PARSE);
        pending = MODE_PARSE;
    } else dn_harness("not a case: %s", line);
    clock_gettime(CLOCK_MONOTONIC, &started);
}

void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen) {
    (void)c, (void)clen, (void)a, (void)alen;
    dn_violation("dn_emit: the article's program has no such call");
}

static void on_exit_run(int code) { dn_violation("the run ended for want of stack or heap (code %d)", code); }

int main(int argc, char **argv) {
    timed = argc == 2 && strcmp(argv[1], "--time") == 0;
    if (argc > 2 || (argc == 2 && !timed)) dn_harness("usage: accept-check [--time]");
    dn_runtime_setup();
    dn_runtime_header();
    fill_heap();
    dn_runtime_on_exit = on_exit_run;
    cml_main();
    dn_violation("the program returned to its host, which a build without --main_return cannot do");
}
