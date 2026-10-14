/* SPDX-License-Identifier: AGPL-3.0-or-later
 * A stand-in for the session's program, linked with the host for the host lane: it calls the host
 * as the program does and prints what the host handed it. A line of standard input is a command:
 *   next          fetch a batch; print `start`, the wall clock, the random octets, the path identity
 *                 and the groups in hexadecimal, then `opened IDX GEN POST` for each connection opened
 *                 and `done SLOT GEN OPS CLASS` and the sixteen result words for each completion,
 *                 and a line `.`
 *   data S AT HEX the bytes of job slot S's data at AT
 *   op S I W...   the ten words of operation I of job slot S
 *   job S GEN N   a job of N operations in slot S, handed with the next emit
 *   emit          hand over the jobs set, and no action
 *   listen W      the word saying whether the host is to listen, from then on (1 at the start)
 *   wake W        the time the next fetch asks to be woken at (else 0)
 *   peek S AT N   print `data` and N bytes of the last completion of slot S from AT, in hexadecimal
 *   stop CODE     stop the run with CODE
 * The symbols a compiled program defines are defined here, so the host and its runtime link. */
#include "cake_runtime.h"
#include "dn_session_layout.h"
#include "host.h"
#include <inttypes.h>

void *cml_heap, *cml_stack, *cml_stackend;
char cake_bitmaps[8], cake_bitmaps_buffer_begin[8], cake_bitmaps_buffer_end[8];
char cake_codebuffer_begin[8], cake_codebuffer_end[8];

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen);
void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen);

static unsigned char *at(size_t offset) { return (unsigned char *)cml_heap + offset; }

static unsigned char *job_slot(uint64_t s) {
    if (s >= DN_SESSION_JOBS) dn_harness("driver: no job slot %" PRIu64, s);
    return at(DN_SESSION_EMIT_OFF + DN_SESSION_EMIT_JOBS + s * DN_SESSION_JOB_SLOT);
}

/* The data of each slot's last completion. */
static unsigned char completed[DN_SESSION_JOBS][DN_SESSION_JOB_DATA];
static uint64_t wake_next;

static void hex(const unsigned char *p, uint64_t n) {
    printf(" ");
    if (!n) printf("-");
    for (uint64_t k = 0; k < n; ++k) printf("%02x", p[k]);
}

static void next(void) {
    unsigned char *a = at(DN_SESSION_NEXT_OFF);
    dn_put_word(a + DN_SESSION_NEXT_WAKE, wake_next);
    wake_next = 0;
    ffidn_next(at(DN_SESSION_CONF_OFF), DN_SESSION_CONF_LEN, a, DN_SESSION_NEXT_LEN);
    uint64_t groups = dn_word(a + DN_SESSION_NEXT_GROUP_COUNT);
    if (groups > DN_SESSION_GROUPS_MAX) dn_violation("%" PRIu64 " groups", groups);
    printf("start %" PRIu64, dn_word(a + DN_SESSION_NEXT_WALL));
    hex(a + DN_SESSION_NEXT_RANDOM, DN_SESSION_RANDOM_LEN);
    hex(a + DN_SESSION_NEXT_IDENTITY, dn_word(a + DN_SESSION_NEXT_IDENTITY_LEN));
    for (uint64_t g = 0; g < groups; ++g) {
        const unsigned char *slot = a + DN_SESSION_NEXT_GROUPS + g * DN_SESSION_GROUP_SLOT;
        hex(slot + 8, dn_word(slot));
    }
    printf("\n");
    for (uint64_t k = 0; k < dn_word(a + DN_SESSION_NEXT_COUNT); ++k) {
        const unsigned char *slot = a + DN_SESSION_NEXT_EVENTS + k * DN_SESSION_EVENT_SLOT;
        if (dn_word(slot + DN_SESSION_EVENT_KIND) == DN_SESSION_OPENED)
            printf("opened %" PRIu64 " %" PRIu64 " %" PRIu64 "\n", dn_word(slot + DN_SESSION_EVENT_IDX),
                   dn_word(slot + DN_SESSION_EVENT_GEN), dn_word(slot + DN_SESSION_EVENT_POST));
    }
    uint64_t done = 0;
    for (uint64_t s = 0; s < DN_SESSION_JOBS; ++s) {
        const unsigned char *slot = a + DN_SESSION_NEXT_DONE + s * DN_SESSION_DONE_SLOT;
        if (dn_word(slot + DN_SESSION_DONE_KIND) != DN_SESSION_DONE) continue;
        ++done;
        printf("done %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64, s, dn_word(slot + DN_SESSION_DONE_GEN),
               dn_word(slot + DN_SESSION_DONE_OPS), dn_word(slot + DN_SESSION_DONE_CLASS));
        for (int w = 0; w < 2 * DN_SESSION_JOB_OPS; ++w)
            printf(" %" PRIu64, dn_word(slot + DN_SESSION_DONE_RESULTS + 8 * w));
        printf("\n");
        memcpy(completed[s], slot + DN_SESSION_DONE_HEAD, DN_SESSION_JOB_DATA);
    }
    if (done != dn_word(a + DN_SESSION_NEXT_DONE_COUNT)) dn_violation("%" PRIu64 " completions counted", done);
    printf(".\n");
}

static void emit(void) {
    unsigned char *a = at(DN_SESSION_EMIT_OFF);
    ffidn_emit(at(DN_SESSION_CONF_OFF), DN_SESSION_CONF_LEN, a, DN_SESSION_EMIT_LEN);
    for (uint64_t s = 0; s < DN_SESSION_JOBS; ++s) dn_put_word(job_slot(s) + DN_SESSION_JOB_KIND, 0);
}

/* The bytes `hex` spells into `p`, at most `room`. */
static void unhex(const char *hex, unsigned char *p, size_t room) {
    size_t n = strlen(hex);
    if (n % 2 || n / 2 > room) dn_harness("driver: %zu hexadecimal digits", n);
    for (size_t k = 0; k < n / 2; ++k) {
        unsigned v;
        if (sscanf(hex + 2 * k, "%2x", &v) != 1) dn_harness("driver: not hexadecimal: %s", hex);
        p[k] = (unsigned char)v;
    }
}

/* The command on `line`, beyond next, emit and stop. */
static void command(char *line) {
    char *word[16] = {0};
    int n = 0;
    for (char *s = strtok(line, " \n"); s && n < 16; s = strtok(NULL, " \n")) word[n++] = s;
    if (!n) dn_harness("driver: an empty command");
    uint64_t w[16] = {0};
    for (int k = 1; k < n; ++k) w[k] = !strcmp(word[0], "data") && k == 3 ? 0 : dn_parse_u64(word[k], UINT64_MAX);
    if (n == 4 && !strcmp(word[0], "data")) {
        if (w[2] > DN_SESSION_JOB_DATA) dn_harness("driver: data at %" PRIu64, w[2]);
        unhex(word[3], job_slot(w[1]) + DN_SESSION_JOB_HEAD + w[2], DN_SESSION_JOB_DATA - w[2]);
    } else if (n == 13 && !strcmp(word[0], "op")) {
        if (w[2] >= DN_SESSION_JOB_OPS) dn_harness("driver: operation %" PRIu64, w[2]);
        unsigned char *o = job_slot(w[1]) + DN_SESSION_JOB_OPS_AT + w[2] * DN_SESSION_OP_SLOT;
        for (int k = 0; k < 10; ++k) dn_put_word(o + 8 * k, w[3 + k]);
    } else if (n == 4 && !strcmp(word[0], "job")) {
        unsigned char *slot = job_slot(w[1]);
        dn_put_word(slot + DN_SESSION_JOB_KIND, DN_SESSION_JOB);
        dn_put_word(slot + DN_SESSION_JOB_GEN, w[2]);
        dn_put_word(slot + DN_SESSION_JOB_COUNT, w[3]);
    } else if (n == 2 && !strcmp(word[0], "wake")) {
        wake_next = w[1];
    } else if (n == 2 && !strcmp(word[0], "listen")) {
        dn_put_word(at(DN_SESSION_EMIT_OFF + DN_SESSION_EMIT_LISTEN), w[1]);
    } else if (n == 4 && !strcmp(word[0], "peek")) {
        if (w[1] >= DN_SESSION_JOBS || w[2] > DN_SESSION_JOB_DATA || w[3] > DN_SESSION_JOB_DATA - w[2])
            dn_harness("driver: peek out of range");
        printf("data");
        hex(completed[w[1]] + w[2], w[3]);
        printf("\n");
    } else {
        dn_harness("driver: no command %s", word[0]);
    }
}

void cml_main(void) {
    memset(at(DN_SESSION_CONF_OFF), 0, DN_SESSION_SIZE - DN_SESSION_CONF_OFF);
    dn_put_word(at(DN_SESSION_CONF_OFF), DN_SESSION_VERSION);
    dn_put_word(at(DN_SESSION_EMIT_OFF + DN_SESSION_EMIT_LISTEN), 1);
    static char line[2 * DN_SESSION_JOB_DATA + 64];
    while (fgets(line, sizeof line, stdin)) {
        if (!strcmp(line, "next\n")) next();
        else if (!strcmp(line, "emit\n")) emit();
        else if (!strncmp(line, "stop ", 5)) {
            line[strcspn(line, "\n")] = 0;
            dn_put_word(at(DN_SESSION_OWN_OFF + DN_SESSION_OWN_STOP), dn_parse_u64(line + 5, UINT64_MAX));
            if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
            cml_exit(0);
        } else {
            command(line);
        }
        if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
    }
    dn_harness("driver: the input ended");
}
