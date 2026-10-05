/* SPDX-License-Identifier: AGPL-3.0-or-later
 * A stand-in for the session's program, linked with the host for the host lane: it calls the host
 * as the program does and prints what the host handed it. A line of standard input is a command:
 *   next          fetch a batch; print `start`, the wall clock, the random octets, the path identity
 *                 and the groups in hexadecimal, then `opened IDX GEN POST` for each connection opened
 *   emit          hand over no action
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

static void hex(const unsigned char *p, uint64_t n) {
    printf(" ");
    if (!n) printf("-");
    for (uint64_t k = 0; k < n; ++k) printf("%02x", p[k]);
}

static void next(void) {
    unsigned char *a = at(DN_SESSION_NEXT_OFF);
    dn_put_word(a + DN_SESSION_NEXT_WAKE, 0);
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
}

static void emit(void) {
    unsigned char *a = at(DN_SESSION_EMIT_OFF);
    memset(a, 0, DN_SESSION_EMIT_LEN);
    ffidn_emit(at(DN_SESSION_CONF_OFF), DN_SESSION_CONF_LEN, a, DN_SESSION_EMIT_LEN);
}

void cml_main(void) {
    memset(at(DN_SESSION_CONF_OFF), 0, DN_SESSION_SIZE - DN_SESSION_CONF_OFF);
    dn_put_word(at(DN_SESSION_CONF_OFF), DN_SESSION_VERSION);
    char line[64];
    while (fgets(line, sizeof line, stdin)) {
        if (!strcmp(line, "next\n")) next();
        else if (!strcmp(line, "emit\n")) emit();
        else if (!strncmp(line, "stop ", 5)) {
            line[strcspn(line, "\n")] = 0;
            dn_put_word(at(DN_SESSION_OWN_OFF + DN_SESSION_OWN_STOP), dn_parse_u64(line + 5, UINT64_MAX));
            if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
            cml_exit(0);
        } else {
            dn_harness("driver: no command %s", line);
        }
        if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
    }
    dn_harness("driver: the input ended");
}
