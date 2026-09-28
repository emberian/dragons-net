/* SPDX-License-Identifier: AGPL-3.0-or-later
 * What the hosts of the server loop share, on top of host.h: the layout the program is written
 * from (dn_layout.h, printed by `dn-compiler emit-layout`), the check that each array the program
 * hands over is the area of the layout it should be, and the heap header. A checking host also
 * fills the heap and the stack before the run — the program's theorem holds for any content — and
 * reads them to see what the program touched; a serving host does neither. */
#ifndef DN_SERVER_H
#define DN_SERVER_H
#include "cake_runtime.h"
#include "dn_layout.h"
#include "host.h"
#include <inttypes.h>

/* The external functions the loop calls; the generated code calls them as C functions. */
void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen);
void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen);

static inline unsigned char *dn_heap_at(size_t offset) { return (unsigned char *)cml_heap + offset; }

/* The configuration array carries the layout's version, and the other array is exactly the area
   of the layout the call is for: the call reads and writes nothing else. */
static inline void dn_call_checked(const unsigned char *c, long clen, const unsigned char *a,
                                   long alen, size_t offset, long len, const char *call) {
    if (c != dn_heap_at(DN_LAYOUT_CONF_OFF) || clen != DN_LAYOUT_CONF_LEN)
        dn_violation("%s: the configuration array is not the layout's", call);
    if (dn_word(c) != DN_LAYOUT_VERSION)
        dn_violation("%s: the program speaks layout %" PRIu64 ", the host %d", call, dn_word(c),
                     DN_LAYOUT_VERSION);
    if (a != dn_heap_at(offset) || alen != len)
        dn_violation("%s: the array is not the layout's area for this call", call);
}

/* The header the compiler theorem requires, which the program has to leave as the start-up code
   found it; checked on every call. */
static inline void dn_header_checked(const char *call) {
    if (!dn_runtime_header_intact())
        dn_violation("%s: the heap header is not what the compiler theorem requires", call);
}

/* The heap past the header and outside the layout's areas is filled before a checked run and has
   to be untouched after each call. Every word of the fill reads as the kind of a received event,
   with two bytes, so a program that strays out of its areas finds plausible work there and gives
   itself away by answering it; a stray write of the fill's own value goes unseen. */
#define DN_SERVER_HEADER_BYTES 40
#define DN_SERVER_FILL_WORD UINT64_C(2)

static inline int dn_in_layout(size_t offset) {
    return (offset >= DN_LAYOUT_CONF_OFF && offset < DN_LAYOUT_CONF_OFF + DN_LAYOUT_CONF_LEN) ||
           (offset >= DN_LAYOUT_NEXT_OFF && offset < DN_LAYOUT_NEXT_OFF + DN_LAYOUT_NEXT_LEN) ||
           (offset >= DN_LAYOUT_EMIT_OFF && offset < DN_LAYOUT_EMIT_OFF + DN_LAYOUT_EMIT_LEN);
}

static inline void dn_fill_heap(void) {
    for (size_t offset = DN_SERVER_HEADER_BYTES; offset < DN_RUNTIME_SEGMENT_BYTES; offset += 8)
        if (!dn_in_layout(offset)) dn_put_word(dn_heap_at(offset), DN_SERVER_FILL_WORD);
}

static inline void dn_fill_checked(const char *call) {
    for (size_t offset = DN_SERVER_HEADER_BYTES; offset < DN_RUNTIME_SEGMENT_BYTES; offset += 8)
        if (!dn_in_layout(offset) && dn_word(dn_heap_at(offset)) != DN_SERVER_FILL_WORD)
            dn_violation("%s: the program wrote outside its layout, at heap offset %zu", call, offset);
}

/* The stack segment is filled with a pattern before the run. CakeML's stack grows down from its
   end, and the start-up code keeps a store at its beginning; each is measured as the words changed
   from its end of the segment up to the first word left as it was, so a frame word the run never
   wrote would cut the measure short. */
#define DN_SERVER_STACK_WORD UINT64_C(0xA5A5A5A5A5A5A5A5)

static inline void dn_fill_stack(void) {
    for (unsigned char *p = cml_stack; p < (unsigned char *)cml_stackend; p += 8)
        dn_put_word(p, DN_SERVER_STACK_WORD);
}

static inline size_t dn_stack_depth(void) {
    const unsigned char *start = cml_stack, *p = cml_stackend;
    while (p > start && dn_word(p - 8) != DN_SERVER_STACK_WORD) p -= 8;
    return (size_t)((const unsigned char *)cml_stackend - p);
}

static inline size_t dn_store_bytes(void) {
    const unsigned char *p = cml_stack, *end = cml_stackend;
    while (p < end && dn_word(p) != DN_SERVER_STACK_WORD) p += 8;
    return (size_t)(p - (const unsigned char *)cml_stack);
}
#endif
