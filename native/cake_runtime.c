/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The one definition of the adapter the generated code links against. */
#include "cake_runtime.h"

void cml_clear(void) {}

void cml_err(int code) { fprintf(stderr, "Cake runtime error %d\n", code); abort(); }

void (*dn_runtime_on_exit)(int code);

void cml_exit(int code) {
    if (dn_runtime_on_exit) dn_runtime_on_exit(code);
    fprintf(stderr, "unexpected Cake exit %d\n", code);
    abort();
}

static void *dn_runtime_memory;

static void dn_runtime_free(void) { free(dn_runtime_memory); }

void dn_runtime_setup_heap(size_t heap_bytes) {
    const size_t segment = DN_RUNTIME_SEGMENT_BYTES;
    if (heap_bytes < segment) abort();
    dn_runtime_memory = malloc(heap_bytes + segment);
    if (!dn_runtime_memory || atexit(dn_runtime_free) != 0) abort();
    cml_heap = dn_runtime_memory;
    cml_stack = (unsigned char *)dn_runtime_memory + heap_bytes;
    cml_stackend = (unsigned char *)dn_runtime_memory + heap_bytes + segment;
}

void dn_runtime_setup(void) { dn_runtime_setup_heap(DN_RUNTIME_SEGMENT_BYTES); }

void dn_runtime_init(void) {
    dn_runtime_setup();
    cml_main();
}
