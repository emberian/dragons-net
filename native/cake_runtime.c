/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The one definition of the adapter the generated code links against. */
#include "cake_runtime.h"

void cml_clear(void) {}

void cml_err(int code) { fprintf(stderr, "Cake runtime error %d\n", code); abort(); }

void cml_exit(int code) { fprintf(stderr, "unexpected Cake exit %d\n", code); abort(); }

static void *dn_runtime_memory;

static void dn_runtime_free(void) { free(dn_runtime_memory); }

void dn_runtime_init(void) {
    const size_t segment = DN_RUNTIME_SEGMENT_BYTES;
    dn_runtime_memory = malloc(2 * segment);
    if (!dn_runtime_memory || atexit(dn_runtime_free) != 0) abort();
    cml_heap = dn_runtime_memory;
    cml_stack = (unsigned char *)dn_runtime_memory + segment;
    cml_stackend = (unsigned char *)dn_runtime_memory + 2 * segment;
    cml_main();
}
