/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Runs the server loop (DN.Server.Skeleton) against a scripted host.
 *   skeleton-check echo
 * hands the program batches of events and requires every received payload back, in order, as a
 * send to the same connection that reads on, then stops the run inside a call.
 *   skeleton-check no-header
 * runs the same script with the heap header left unwritten, which the first call has to report.
 *   skeleton-check count-negative|count-over|length-negative|length-over
 * hands it one batch whose count of events, or one of whose lengths, is just out of range, and
 * requires the run to end there instead of going on. Before the run the heap outside the layout is
 * filled and the stack patterned; on every call the fill and the heap header have to be intact. */
#include "server.h"

struct event {
    uint64_t kind, index, generation;
    int64_t length;
    unsigned char fill;
};

#define MAX_EVENTS DN_LAYOUT_BATCH

static const char *mode;
static int hostile, handed_hostile, awaiting_emit, batches_done;

static unsigned long echoed;
static struct event current[MAX_EVENTS];
static long current_count;

static unsigned char payload_byte(const struct event *e, long j) { return (unsigned char)(e->fill + j); }

static void put_events(unsigned char *a, int64_t count, const struct event *events, long n) {
    dn_put_word(a, (uint64_t)count);
    dn_put_word(a + DN_LAYOUT_NEXT_CLOCK, (uint64_t)batches_done * 1000);
    for (long i = 0; i < n; ++i) {
        unsigned char *slot = a + DN_LAYOUT_NEXT_EVENTS + i * DN_LAYOUT_EVENT_SLOT;
        dn_put_word(slot + DN_LAYOUT_EVENT_KIND, events[i].kind);
        dn_put_word(slot + DN_LAYOUT_EVENT_IDX, events[i].index);
        dn_put_word(slot + DN_LAYOUT_EVENT_GEN, events[i].generation);
        dn_put_word(slot + DN_LAYOUT_EVENT_LEN, (uint64_t)events[i].length);
        long bytes = events[i].length < 0 ? 0 : events[i].length > DN_LAYOUT_DATA ? DN_LAYOUT_DATA : events[i].length;
        for (long j = 0; j < bytes; ++j) slot[DN_LAYOUT_EVENT_HEAD + j] = payload_byte(&events[i], j);
    }
    memcpy(current, events, (size_t)n * sizeof *events);
    current_count = n;
}

/* The scripted batches of the echo run. */
static long echo_batch(int number, struct event *events) {
    switch (number) {
    case 0:
        events[0] = (struct event){DN_LAYOUT_RECEIVED, 0, 1, 5, 'h'};
        return 1;
    case 1:
        events[0] = (struct event){DN_LAYOUT_OPENED, 3, 7, 0, 0};
        events[1] = (struct event){DN_LAYOUT_RECEIVED, 3, 7, DN_LAYOUT_DATA, 0};
        events[2] = (struct event){DN_LAYOUT_WRITABLE, 0, 1, 0, 0};
        events[3] = (struct event){DN_LAYOUT_RECEIVED, 0, 1, 0, 0};
        events[4] = (struct event){DN_LAYOUT_INPUT_ENDED, 3, 7, 0, 0};
        events[5] = (struct event){DN_LAYOUT_CLOSED, 0, 1, 0, 0};
        return 6;
    case 2:
        for (long i = 0; i < MAX_EVENTS; ++i)
            events[i] = (struct event){DN_LAYOUT_RECEIVED, (uint64_t)i, (uint64_t)(i + 1),
                                       i * 31 % (DN_LAYOUT_DATA + 1), (unsigned char)i};
        return MAX_EVENTS;
    case 3:
        return 0;
    default:
        return -1;
    }
}

/* The one batch of a hostile run. */
static void hostile_batch(unsigned char *a) {
    struct event events[MAX_EVENTS];
    for (long i = 0; i < MAX_EVENTS; ++i) events[i] = (struct event){DN_LAYOUT_RECEIVED, 0, 1, 0, 0};
    if (strcmp(mode, "count-negative") == 0) put_events(a, -1, events, 1);
    else if (strcmp(mode, "count-over") == 0) put_events(a, MAX_EVENTS + 1, events, MAX_EVENTS);
    else if (strcmp(mode, "length-negative") == 0) {
        events[0].length = -1;
        put_events(a, 1, events, 1);
    } else {
        /* The last slot, so that a program that copies past its bytes leaves the layout. */
        events[MAX_EVENTS - 1].length = DN_LAYOUT_DATA + 1;
        put_events(a, MAX_EVENTS, events, MAX_EVENTS);
    }
    handed_hostile = 1;
}

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen) {
    dn_header_checked("dn_next");
    dn_call_checked(c, clen, a, alen, DN_LAYOUT_NEXT_OFF, DN_LAYOUT_NEXT_LEN, "dn_next");
    dn_fill_checked("dn_next");
    if (handed_hostile) dn_violation("dn_next: the program went on after a %s batch", mode);
    if (awaiting_emit) dn_violation("dn_next: the program fetched again without handing over its answers");
    if (hostile) {
        hostile_batch(a);
    } else {
        struct event events[MAX_EVENTS];
        long n = echo_batch(batches_done, events);
        if (n < 0) {
            /* The script is done: the host ends the run inside the call, as a server host would. */
            printf("{\"mode\": \"%s\", \"batches\": %d, \"echoed\": %lu, \"stack_depth\": %zu, "
                   "\"store_bytes\": %zu}\n", mode, batches_done, echoed, dn_stack_depth(), dn_store_bytes());
            exit(0);
        }
        put_events(a, n, events, n);
    }
    awaiting_emit = 1;
}

void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen) {
    dn_header_checked("dn_emit");
    dn_call_checked(c, clen, a, alen, DN_LAYOUT_EMIT_OFF, DN_LAYOUT_EMIT_LEN, "dn_emit");
    dn_fill_checked("dn_emit");
    if (handed_hostile) dn_violation("dn_emit: the program went on after a %s batch", mode);
    if (!awaiting_emit) dn_violation("dn_emit: the program answered without fetching");
    long expected = 0;
    for (long i = 0; i < current_count; ++i) expected += current[i].kind == DN_LAYOUT_RECEIVED;
    if (dn_word(a) != (uint64_t)expected)
        dn_violation("dn_emit: %" PRIu64 " actions for %ld received payloads", dn_word(a), expected);
    if (dn_word(a + DN_LAYOUT_EMIT_WAKE) != 0) dn_violation("dn_emit: a deadline the loop has no reason for");
    long action = 0;
    for (long i = 0; i < current_count; ++i) {
        const struct event *e = &current[i];
        if (e->kind != DN_LAYOUT_RECEIVED) continue;
        unsigned char *slot = a + DN_LAYOUT_EMIT_ACTIONS + action * DN_LAYOUT_ACTION_SLOT;
        if (dn_word(slot + DN_LAYOUT_ACTION_KIND) != DN_LAYOUT_SEND)
            dn_violation("dn_emit: action %ld is not a send", action);
        if (dn_word(slot + DN_LAYOUT_ACTION_IDX) != e->index)
            dn_violation("dn_emit: action %ld names another connection than payload %ld", action, i);
        if (dn_word(slot + DN_LAYOUT_ACTION_GEN) != e->generation)
            dn_violation("dn_emit: action %ld names another generation than payload %ld", action, i);
        if (dn_word(slot + DN_LAYOUT_ACTION_LEN) != (uint64_t)e->length)
            dn_violation("dn_emit: action %ld has another length than payload %ld", action, i);
        if (dn_word(slot + DN_LAYOUT_ACTION_READ) != 1) dn_violation("dn_emit: action %ld does not read on", action);
        if (dn_word(slot + DN_LAYOUT_ACTION_TAKEN) != 0)
            dn_violation("dn_emit: action %ld claims bytes the host has not taken", action);
        for (long j = 0; j < e->length; ++j)
            if (slot[DN_LAYOUT_ACTION_HEAD + j] != payload_byte(e, j))
                dn_violation("dn_emit: action %ld differs from its payload at byte %ld", action, j);
        dn_put_word(slot + DN_LAYOUT_ACTION_TAKEN, (uint64_t)e->length);
        ++action;
    }
    echoed += (unsigned long)action;
    ++batches_done;
    awaiting_emit = 0;
}

static void on_exit_run(int code) {
    if (code != 0) dn_violation("the run ended for want of stack or heap (code %d)", code);
    if (!handed_hostile) dn_violation("the program ended its run without a cause");
    dn_header_checked("end of run");
    dn_fill_checked("end of run");
    printf("{\"mode\": \"%s\", \"ended\": true}\n", mode);
    exit(0);
}

int main(int argc, char **argv) {
    if (argc != 2)
        dn_harness("usage: skeleton-check echo|no-header|count-negative|count-over|length-negative|length-over");
    mode = argv[1];
    int header_written = strcmp(mode, "no-header") != 0;
    hostile = strcmp(mode, "echo") != 0 && header_written;
    if (hostile && strcmp(mode, "count-negative") && strcmp(mode, "count-over") &&
        strcmp(mode, "length-negative") && strcmp(mode, "length-over"))
        dn_harness("skeleton-check: no mode %s", mode);
    dn_runtime_setup();
    if (header_written) dn_runtime_header();
    dn_fill_heap();
    dn_fill_stack();
    dn_runtime_on_exit = on_exit_run;
    cml_main();
    dn_violation("the program returned to its host, which a build without --main_return cannot do");
}
