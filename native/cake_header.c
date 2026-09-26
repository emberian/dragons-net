/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The heap header CakeML's compiler theorem requires when the program is entered (the premise
 * `pan_installed`): the addresses of the compiled bitmaps, the two ends of the data buffer after
 * them and the two ends of the code buffer, in the first five words of the heap. The start-up code
 * of an ML program writes them; that of a Pancake program only reads them, so the host has to.
 * `cake_bitmaps` is a local label in the emitted assembly, and a program linked with this file has
 * to be assembled with that label made global. */
#include "cake_runtime.h"
#include <string.h>

extern char cake_bitmaps[], cake_bitmaps_buffer_begin[], cake_bitmaps_buffer_end[];
extern char cake_codebuffer_begin[], cake_codebuffer_end[];

static const void *header_word(int i) {
    const void *const words[] = {cake_bitmaps, cake_bitmaps_buffer_begin, cake_bitmaps_buffer_end,
                                 cake_codebuffer_begin, cake_codebuffer_end};
    return words[i];
}

/* Call after dn_runtime_setup and before cml_main. */
void dn_runtime_header(void) {
    for (int i = 0; i < 5; ++i) {
        const void *word = header_word(i);
        memcpy((unsigned char *)cml_heap + 8 * i, &word, sizeof word);
    }
}

/* Whether the five words still hold those addresses. */
int dn_runtime_header_intact(void) {
    for (int i = 0; i < 5; ++i) {
        const void *word;
        memcpy(&word, (const unsigned char *)cml_heap + 8 * i, sizeof word);
        if (word != header_word(i)) return 0;
    }
    return 1;
}
