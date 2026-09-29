/* SPDX-License-Identifier: AGPL-3.0-or-later
 * What each host of the session's program checks on every external call (call_checks.h), with the
 * session's layout; and what its code relies on of that layout, checked when it is compiled. */
#ifndef DN_SESSION_CALLS_H
#define DN_SESSION_CALLS_H
#include "call_checks.h"
#include "dn_session_layout.h"

_Static_assert(DN_HEADER_BYTES <= DN_SESSION_CONF_OFF, "the layout overlaps the heap header");
_Static_assert(DN_SESSION_SIZE <= DN_RUNTIME_SEGMENT_BYTES, "the layout does not fit the heap segment");
_Static_assert(DN_SESSION_EVENT_HEAD + DN_SESSION_DATA <= DN_SESSION_EVENT_SLOT, "an event's data overruns its slot");
_Static_assert(DN_SESSION_ACTION_HEAD + DN_SESSION_DATA <= DN_SESSION_ACTION_SLOT,
               "an action's data overruns its slot");
_Static_assert(DN_SESSION_NEXT_EVENTS + DN_SESSION_BATCH * DN_SESSION_EVENT_SLOT <= DN_SESSION_NEXT_LEN,
               "a batch of events overruns its area");
_Static_assert(DN_SESSION_EMIT_ACTIONS + DN_SESSION_CONNS * DN_SESSION_ACTION_SLOT <= DN_SESSION_EMIT_LEN,
               "the actions overrun their area");
_Static_assert(DN_SESSION_NEXT_REV + DN_SESSION_REV_MAX <= DN_SESSION_NEXT_SRC_LEN, "the revision overruns its place");
_Static_assert(DN_SESSION_NEXT_SRC + DN_SESSION_SRC_MAX <= DN_SESSION_NEXT_EVENTS, "the source overruns its place");
/* The program writes its texts a word at a time, their first byte lowest. */
_Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "the program's texts are laid out little-endian");

static inline void dn_session_call(const unsigned char *c, long clen, const unsigned char *a, long alen,
                                   size_t offset, long len, const char *call) {
    dn_header_checked(call);
    dn_arrays_checked(c, clen, a, alen, DN_SESSION_CONF_OFF, DN_SESSION_CONF_LEN, DN_SESSION_VERSION, offset,
                      len, call);
}

#endif
