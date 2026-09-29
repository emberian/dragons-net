/* SPDX-License-Identifier: AGPL-3.0-or-later
 * What every host of a whole program checks on each external call, whatever its layout: the heap
 * header the compiler theorem requires, the configuration array and the layout version in it, and
 * that the other array is the layout's area for the call. */
#ifndef DN_CALL_CHECKS_H
#define DN_CALL_CHECKS_H
#include "cake_runtime.h"
#include "host.h"
#include <inttypes.h>

/* The external functions the program calls; the generated code calls them as C functions. */
void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen);
void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen);

/* The five words at the start of the heap the compiler theorem requires (cake_header.c). */
enum { DN_HEADER_BYTES = 40 };

static inline unsigned char *dn_heap_at(size_t offset) { return (unsigned char *)cml_heap + offset; }

static inline void dn_header_checked(const char *call) {
    if (!dn_runtime_header_intact())
        dn_violation("%s: the heap header is not what the compiler theorem requires", call);
}

/* The configuration array is `conf_len` bytes at `conf_off` and carries `version`; the other array
   is `len` bytes at `offset`: the call reads and writes nothing else. */
static inline void dn_arrays_checked(const unsigned char *c, long clen, const unsigned char *a,
                                     long alen, size_t conf_off, long conf_len, uint64_t version,
                                     size_t offset, long len, const char *call) {
    if (c != dn_heap_at(conf_off) || clen != conf_len)
        dn_violation("%s: the configuration array is not the layout's", call);
    if (dn_word(c) != version)
        dn_violation("%s: the program speaks layout %" PRIu64 ", the host %" PRIu64, call, dn_word(c),
                     version);
    if (a != dn_heap_at(offset) || alen != len)
        dn_violation("%s: the array is not the layout's area for this call", call);
}
#endif
