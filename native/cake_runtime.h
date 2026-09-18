/* Trusted, single-threaded Linux x86-64 adapter. Not a verified allocator. */
#ifndef DN_CAKE_RUNTIME_H
#define DN_CAKE_RUNTIME_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);
void cml_clear(void) {}
void cml_err(int code) { fprintf(stderr, "Cake runtime error %d\n", code); abort(); }
void cml_exit(int code) { fprintf(stderr, "unexpected Cake exit %d\n", code); abort(); }
static void *dn_runtime_memory;
static void dn_runtime_free(void) { free(dn_runtime_memory); }
static void dn_runtime_init(void) {
    const size_t segment = 1024 * 1024;
    dn_runtime_memory = malloc(2 * segment);
    if (!dn_runtime_memory || atexit(dn_runtime_free) != 0) abort();
    cml_heap = dn_runtime_memory;
    cml_stack = (unsigned char *)dn_runtime_memory + segment;
    cml_stackend = (unsigned char *)dn_runtime_memory + 2 * segment;
    cml_main();
}
#endif
