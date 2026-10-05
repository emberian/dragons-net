/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Runs the NNTP session (DN.Server.Session) as `dn-compiler session-model` runs its model: it reads
 * the same lines from stdin and answers with the same lines, so that one driver can hold the
 * compiled code against the model turn by turn (scripts/session_native.py).
 *
 *   identity REVISION SOURCE        once, first; both in hex
 *   turn NOW, then events, then go  a batch; the answer is the actions, then `done`
 *   took N ...                      what the kernel took of each send; the answer, `deadline D`,
 *                                   comes when the program asks for its next batch
 *
 * Besides the events the model knows, a batch can hold `raw KIND IDX GEN`, an event of any kind,
 * and `poke OFFSET VALUE`, a word the host writes into the program's own area, and an identity can
 * be longer than the layout holds, its length written in full: all are there to break the contract
 * in ways only the program is asked to see.
 *
 * A breach ends the run with the code the program leaves in its area, answered `stop CODE`. A
 * `took` with another number of counts than sends cannot be written in the layout, where each
 * count lies in its send's slot; the host answers it itself, as the model does. The end of stdin
 * ends the run inside a call, as a serving host would.
 *
 * Before the run the whole heap past its header is filled, so the program cannot lean on what it
 * did not write; on every call and when the run ends, the heap header, the heap before the first
 * area and the heap past the program's layout have to be as they were, and each array the program
 * hands over has to be its area of the layout. */
#include "session_calls.h"

enum { MAX_LINE = 1 << 16 };
static const uint64_t FILL = UINT64_C(0x5A5A5A5A5A5A5A5A);

static unsigned char revision[DN_SESSION_REV_MAX], source[DN_SESSION_SRC_MAX];
static size_t revision_len, source_len;
static int started, awaiting_emit;
static long sends;
static char line[MAX_LINE];

/* The heap outside the program's areas: the header, the bytes before the first area, and all past
 * the layout. */
static void heap_intact(const char *call) {
    dn_header_checked(call);
    for (size_t off = DN_HEADER_BYTES; off < DN_SESSION_CONF_OFF; off += 8)
        if (dn_word(dn_heap_at(off)) != FILL)
            dn_violation("%s: the program wrote before its layout, at heap offset %zu", call, off);
    for (size_t off = DN_SESSION_SIZE; off < DN_SESSION_HEAP_BYTES; off += 8)
        if (dn_word(dn_heap_at(off)) != FILL)
            dn_violation("%s: the program wrote past its layout, at heap offset %zu", call, off);
}

static void checked(const unsigned char *c, long clen, const unsigned char *a, long alen, size_t offset, long len,
                    const char *call) {
    heap_intact(call);
    dn_session_call(c, clen, a, alen, offset, len, call);
}

static char *next_line(void) {
    if (!fgets(line, sizeof line, stdin)) {
        if (ferror(stdin)) dn_harness("stdin: %s", strerror(errno));
        return NULL;
    }
    size_t n = strlen(line);
    if (n && line[n - 1] == '\n') line[--n] = 0;
    else if (!feof(stdin)) dn_harness("bad input: a line of %d characters or more", MAX_LINE - 1);
    return line;
}

static uint64_t number(const char *text) { return dn_parse_u64(text, UINT64_MAX); }

static int nibble(char h) {
    if (h >= '0' && h <= '9') return h - '0';
    if (h >= 'a' && h <= 'f') return h - 'a' + 10;
    dn_harness("bad input: not hex: %c", h);
}

/* Hex bytes into `out`, at most `room` of them; the count in full, `-` being none. */
static size_t unhex(const char *text, unsigned char *out, size_t room) {
    if (strcmp(text, "-") == 0) return 0;
    size_t digits = strlen(text);
    if (digits % 2) dn_harness("bad input: an odd number of hex digits");
    for (size_t k = 0; k < digits / 2 && k < room; ++k)
        out[k] = (unsigned char)(nibble(text[2 * k]) * 16 + nibble(text[2 * k + 1]));
    return digits / 2;
}

static void print_hex(const unsigned char *bytes, uint64_t count) {
    if (count == 0) putchar('-');
    for (uint64_t k = 0; k < count; ++k) printf("%02x", bytes[k]);
}

static void answer(void) {
    if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
}

static const char *const kinds[] = {"open", "recv", "writable", "end", "closed"};

static size_t smaller(size_t a, size_t b) { return a < b ? a : b; }

/* One batch from stdin into the `dn_next` array; the end of stdin ends the run. */
static void batch(unsigned char *a) {
    char *text = next_line();
    if (!text) exit(0);
    char *word = strtok(text, " "), *now = strtok(NULL, " ");
    if (!word || strcmp(word, "turn") || !now || strtok(NULL, " ")) dn_harness("bad input: not a turn");
    dn_put_word(a + DN_SESSION_NEXT_CLOCK, number(now));
    dn_put_word(a + DN_SESSION_NEXT_REV_LEN, revision_len);
    memcpy(a + DN_SESSION_NEXT_REV, revision, smaller(revision_len, sizeof revision));
    dn_put_word(a + DN_SESSION_NEXT_SRC_LEN, source_len);
    memcpy(a + DN_SESSION_NEXT_SRC, source, smaller(source_len, sizeof source));
    uint64_t count = 0;
    while ((text = next_line()) && strcmp(text, "go")) {
        if (strncmp(text, "poke ", 5) == 0) {
            char *off = strtok(text + 5, " "), *value = strtok(NULL, " ");
            if (!off || !value || strtok(NULL, " ")) dn_harness("bad input: not a poke");
            uint64_t at = number(off);
            if (at < DN_SESSION_OWN_OFF || at >= DN_SESSION_SIZE || at % 8)
                dn_harness("bad input: a poke outside the program's own area");
            dn_put_word(dn_heap_at(at), number(value));
            continue;
        }
        char *kind = strtok(text, " "), *raw = kind && strcmp(kind, "raw") == 0 ? strtok(NULL, " ") : NULL;
        char *idx = strtok(NULL, " "), *gen = strtok(NULL, " "), *data = strtok(NULL, " ");
        if (!kind || !idx || !gen || (strcmp(kind, "raw") == 0 && !raw))
            dn_harness("bad input: an event without its connection");
        uint64_t code = raw ? number(raw) : 0;
        for (uint64_t k = 0; !raw && k < 5; ++k)
            if (strcmp(kind, kinds[k]) == 0) code = k + 1;
        if (raw ? data != NULL : (!code || (code == DN_SESSION_RECEIVED) != (data != NULL)))
            dn_harness("bad input: no event %s", kind);
        if (count < DN_SESSION_BATCH) {
            unsigned char *slot = a + DN_SESSION_NEXT_EVENTS + count * DN_SESSION_EVENT_SLOT;
            dn_put_word(slot + DN_SESSION_EVENT_KIND, code);
            dn_put_word(slot + DN_SESSION_EVENT_IDX, number(idx));
            dn_put_word(slot + DN_SESSION_EVENT_GEN, number(gen));
            dn_put_word(slot + DN_SESSION_EVENT_POST, 0);
            dn_put_word(slot + DN_SESSION_EVENT_LEN,
                        data ? unhex(data, slot + DN_SESSION_EVENT_HEAD, DN_SESSION_DATA) : 0);
        }
        ++count;
    }
    if (!text) dn_harness("bad input: the input ended inside a turn");
    dn_put_word(a + DN_SESSION_NEXT_COUNT, count);
}

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen) {
    checked(c, clen, a, alen, DN_SESSION_NEXT_OFF, DN_SESSION_NEXT_LEN, "dn_next");
    if (awaiting_emit) dn_violation("dn_next: the program fetched again without handing over its answers");
    if (started) {
        printf("deadline %" PRIu64 "\n", dn_word(a + DN_SESSION_NEXT_WAKE));
        answer();
    }
    started = 1;
    batch(a);
    awaiting_emit = 1;
}

void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen) {
    checked(c, clen, a, alen, DN_SESSION_EMIT_OFF, DN_SESSION_EMIT_LEN, "dn_emit");
    if (!awaiting_emit) dn_violation("dn_emit: the program answered without fetching");
    uint64_t count = dn_word(a + DN_SESSION_EMIT_COUNT), actions = 0;
    sends = 0;
    for (uint64_t k = 0; k < DN_SESSION_CONNS; ++k) {
        unsigned char *slot = a + DN_SESSION_EMIT_ACTIONS + k * DN_SESSION_ACTION_SLOT;
        uint64_t kind = dn_word(slot + DN_SESSION_ACTION_KIND), idx = dn_word(slot + DN_SESSION_ACTION_IDX),
                 gen = dn_word(slot + DN_SESSION_ACTION_GEN), len = dn_word(slot + DN_SESSION_ACTION_LEN);
        if (kind == 0) continue;
        ++actions;
        if (idx != k) dn_violation("dn_emit: the slot of connection %" PRIu64 " holds an action for %" PRIu64, k, idx);
        if (kind == DN_SESSION_SEND) {
            uint64_t read = dn_word(slot + DN_SESSION_ACTION_READ);
            if (len > DN_SESSION_DATA) dn_violation("dn_emit: a send of %" PRIu64 " bytes", len);
            if (read > 1) dn_violation("dn_emit: a send whose word to read is %" PRIu64, read);
            printf("send %" PRIu64 " %" PRIu64 " ", idx, gen);
            print_hex(slot + DN_SESSION_ACTION_HEAD, len);
            printf(" %" PRIu64 "\n", read);
            ++sends;
        } else if (kind == DN_SESSION_CLOSE_GRACEFULLY) {
            printf("graceful %" PRIu64 " %" PRIu64 "\n", idx, gen);
        } else if (kind == DN_SESSION_CLOSE_NOW) {
            printf("close %" PRIu64 " %" PRIu64 "\n", idx, gen);
        } else {
            dn_violation("dn_emit: an action of kind %" PRIu64, kind);
        }
    }
    if (actions != count)
        dn_violation("dn_emit: %" PRIu64 " actions counted, %" PRIu64 " in the slots", count, actions);
    printf("done\n");
    answer();
    char *text = next_line();
    char *word = text ? strtok(text, " ") : NULL;
    if (!word || strcmp(word, "took")) dn_harness("bad input: no took after the actions");
    long found = 0;
    for (uint64_t k = 0; k < DN_SESSION_CONNS; ++k) {
        unsigned char *slot = a + DN_SESSION_EMIT_ACTIONS + k * DN_SESSION_ACTION_SLOT;
        if (dn_word(slot + DN_SESSION_ACTION_KIND) != DN_SESSION_SEND) continue;
        char *taken = strtok(NULL, " ");
        if (!taken) break;
        dn_put_word(slot + DN_SESSION_ACTION_TAKEN, number(taken));
        ++found;
    }
    if (found != sends || strtok(NULL, " ")) {
        printf("stop %d\n", DN_SESSION_OVER_TAKEN);
        answer();
        exit(0);
    }
    awaiting_emit = 0;
}

__attribute__((noreturn)) static void on_exit_run(int code) {
    if (code != 0) dn_violation("the run ended for want of stack or heap (code %d)", code);
    heap_intact("the end of the run");
    uint64_t stop = dn_word(dn_heap_at(DN_SESSION_OWN_OFF + DN_SESSION_OWN_STOP));
    if (stop == 0) dn_violation("the program ended its run without a cause");
    printf("stop %" PRIu64 "\n", stop);
    answer();
    exit(0);
}

int main(void) {
    char *text = next_line();
    if (!text) dn_harness("bad input: no identity first");
    char *word = strtok(text, " "), *rev = strtok(NULL, " "), *src = strtok(NULL, " ");
    if (!word || strcmp(word, "identity") || !rev || !src || strtok(NULL, " "))
        dn_harness("bad input: no identity first");
    revision_len = unhex(rev, revision, sizeof revision);
    source_len = unhex(src, source, sizeof source);
    dn_expect_faults();
    dn_runtime_setup_heap(DN_SESSION_HEAP_BYTES);
    dn_runtime_header();
    for (size_t off = DN_HEADER_BYTES; off < DN_SESSION_HEAP_BYTES; off += 8) dn_put_word(dn_heap_at(off), FILL);
    dn_runtime_on_exit = on_exit_run;
    cml_main();
    dn_violation("the program returned to its host, which a build without --main_return cannot do");
}
