/* Trusted, single-threaded Linux x86-64 adapter. Not a verified allocator. */
#ifndef DN_CAKE_RUNTIME_H
#define DN_CAKE_RUNTIME_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);

/* Called by the generated code; defined once, in cake_runtime.c. */
void cml_clear(void);
void cml_err(int code);
void cml_exit(int code);

/* The adapter provisions this much for each of the heap and the stack. */
#define DN_RUNTIME_SEGMENT_BYTES (1024u * 1024u)

/* Give the generated code its heap and stack, then enter it. */
void dn_runtime_init(void);

#endif
