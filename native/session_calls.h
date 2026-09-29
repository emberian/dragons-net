/* SPDX-License-Identifier: AGPL-3.0-or-later
 * What each host of the session's program checks on every external call: the heap header the
 * compiler theorem requires, the configuration array and the layout version in it, and that the
 * array handed over is the layout's area for the call. */
#ifndef DN_SESSION_CALLS_H
#define DN_SESSION_CALLS_H
#include "cake_runtime.h"
#include "dn_session_layout.h"
#include "host.h"
#include <inttypes.h>

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen);
void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen);

_Static_assert(DN_SESSION_SIZE <= DN_RUNTIME_SEGMENT_BYTES, "the layout does not fit the heap segment");

static inline unsigned char *dn_heap_at(size_t offset) { return (unsigned char *)cml_heap + offset; }

static inline void dn_session_call(const unsigned char *c, long clen, const unsigned char *a, long alen,
                                   size_t offset, long len, const char *call) {
    if (!dn_runtime_header_intact()) dn_violation("%s: the heap header is not what the compiler theorem requires", call);
    if (c != dn_heap_at(DN_SESSION_CONF_OFF) || clen != DN_SESSION_CONF_LEN)
        dn_violation("%s: the configuration array is not the layout's", call);
    if (dn_word(c) != DN_SESSION_VERSION)
        dn_violation("%s: the program speaks layout %" PRIu64 ", the host %d", call, dn_word(c), DN_SESSION_VERSION);
    if (a != dn_heap_at(offset) || alen != len) dn_violation("%s: the array is not the layout's area for this call", call);
}

#endif
