/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The emitted recovery against `dn-compiler recovery-model`: each line of standard input is the
 * configuration's key and groups, a directory — names and octets, as `recover` lines give them —
 * and what the model finds there. Stepped as a caller does, recovery asks for the directory's
 * names, the journal's length and octets, final files and names set aside, and gives its actions,
 * the numbers set aside and the store, or why it does not start: it has to find what the model
 * finds. Its area ends at a page without access, and what it points to has to lie in it. */
#define _GNU_SOURCE
#include "cake_runtime.h"
#include "dn_recover_layout.h"
#include "dn_scan_layout.h"
#include "host.h"
#include <inttypes.h>
extern uint32_t dn_recover_step(uint64_t area);

struct entry {
    unsigned char *name, *data;
    size_t name_len, len;
};

static struct entry *dir;
static size_t entries, entries_cap;
static char *said;
static size_t said_len, said_cap;

static void say(const char *text, size_t n) {
    if (said_len + n + 1 > said_cap) {
        said_cap = 2 * (said_len + n + 1);
        said = realloc(said, said_cap);
        if (!said) dn_harness("out of memory");
    }
    memcpy(said + said_len, text, n);
    said_len += n;
    said[said_len] = 0;
}

static void sayf(const char *format, ...) __attribute__((format(printf, 1, 2)));
static void sayf(const char *format, ...) {
    char text[64];
    va_list args;
    va_start(args, format);
    int n = vsnprintf(text, sizeof text, format, args);
    va_end(args);
    say(text, (size_t)n);
}

static void say_hex(const unsigned char *p, uint64_t n) {
    static const char digits[] = "0123456789abcdef";
    if (!n) say("-", 1);
    for (uint64_t i = 0; i < n; ++i) say((char[]){digits[p[i] >> 4], digits[p[i] & 15]}, 2);
}

/* A name the store gives: its letter and sixteen hexadecimal digits. */
static void say_name(char letter, uint64_t seq) {
    char name[18];
    snprintf(name, sizeof name, "%c%016" PRIx64, letter, seq);
    say_hex((const unsigned char *)name, 17);
}

/* The octets of `hex` into a new buffer; their number into `n`. */
static unsigned char *unhex(const char *hex, size_t len, size_t *n) {
    if (len == 1 && hex[0] == '-') len = 0;
    if (len % 2) dn_harness("hexadecimal of odd length");
    unsigned char *out = malloc(len / 2 + 1);
    if (!out) dn_harness("out of memory");
    for (size_t i = 0; i < len / 2; ++i) {
        unsigned v;
        if (sscanf(hex + 2 * i, "%2x", &v) != 1) dn_harness("not hexadecimal");
        out[i] = (unsigned char)v;
    }
    *n = len / 2;
    return out;
}

static const struct entry *lookup(const char *name, size_t n) {
    for (size_t i = 0; i < entries; ++i)
        if (dir[i].name_len == n && !memcmp(dir[i].name, name, n)) return &dir[i];
    return NULL;
}

static const struct entry *named(char letter, uint64_t seq) {
    char name[18];
    snprintf(name, sizeof name, "%c%016" PRIx64, letter, seq);
    return lookup(name, 17);
}

/* The `n` octets at offset `at` of the area, which have to lie in it. */
static const unsigned char *in_area(const unsigned char *a, uint64_t at, uint64_t n) {
    if (n > DN_RECOVER_AREA || at > DN_RECOVER_AREA - n) dn_violation("recovery points outside its area");
    return a + at;
}

static const char *const why[] = {"", "short", "too-long", "unterminated", "tag", "not-a-record", "format-again"};

static void fault(const unsigned char *a) {
    uint64_t at = dn_word(a + DN_RECOVER_FAULT_AT), len = dn_word(a + DN_RECOVER_FAULT_LEN);
    uint64_t x = dn_word(a + DN_RECOVER_FAULT_A), y = dn_word(a + DN_RECOVER_FAULT_B);
    say("corrupt ", 8);
    switch (dn_word(a + DN_RECOVER_FAULT)) {
    case 1:
        say("bad-name ", 9);
        say_hex(a + DN_RECOVER_NAME, dn_word(a + DN_RECOVER_NAME_LEN));
        break;
    case 2: say("no-journal", 10); break;
    case 3:
        if (y - 1 >= 6) dn_violation("a journal corrupt for reason %" PRIu64, y);
        sayf("journal %" PRIu64 " %s", x, why[y]);
        break;
    case 4: sayf("seq-twice %" PRIu64, x); break;
    case 5:
        say("number-not-above ", 17);
        say_hex(in_area(a, at, len), len);
        sayf(" %" PRIu64, x);
        break;
    case 6:
        say("unknown-group ", 14);
        say_hex(in_area(a, at, len), len);
        break;
    case 7: sayf("missing-file %" PRIu64, x); break;
    case 8: sayf("wrong-size %" PRIu64, x); break;
    case 9: say("exhausted", 9); break;
    case 11: sayf("too-many %" PRIu64, x); break;
    case 12:
        say("id-twice ", 9);
        say_hex(in_area(a, at, len), len);
        break;
    default: dn_violation("recovery refused for reason %" PRIu64, dn_word(a + DN_RECOVER_FAULT));
    }
}

static void articles(const unsigned char *a) {
    uint64_t commits = dn_word(a + DN_RECOVER_COMMITS);
    if (commits > DN_RECOVER_CAPACITY) dn_violation("a store of %" PRIu64 " commits", commits);
    if (!commits) say("-", 1);
    for (uint64_t i = 0; i < commits; ++i) {
        const unsigned char *slot = a + DN_RECOVER_SLOTS + i * DN_RECOVER_SLOT_SIZE;
        uint64_t sizes = dn_word(slot + DN_RECOVER_SLOT_SIZES), misc = dn_word(slot + DN_RECOVER_SLOT_MISC);
        uint64_t groups = misc & 255, id_len = (misc >> 8) & 255;
        if (i) say(";", 1);
        sayf("C:%" PRIu64 ":", dn_word(slot + DN_RECOVER_SLOT_SEQ));
        say_hex(slot + DN_RECOVER_SLOT_ID, id_len);
        sayf(":%" PRIu64 ":%" PRIu64 ":%" PRIu64 ":", sizes >> 32, sizes & 0xffffffff, misc >> 16);
        for (uint64_t g = 0; g < groups; ++g) {
            uint64_t w = dn_word(slot + DN_RECOVER_SLOT_GROUPS + 8 * g), k = w >> 32;
            if (k >= dn_word(a + DN_RECOVER_GROUP_COUNT)) dn_violation("a group of index %" PRIu64, k);
            const unsigned char *group = a + DN_RECOVER_GROUPS + k * DN_RECOVER_GROUP_SLOT;
            if (g) say(",", 1);
            say_hex(group + 8, dn_word(group));
            sayf("=%" PRIu64, w & 0xffffffff);
        }
    }
}

/* One directory recovered; its answer in `said`. */
static void recover(const unsigned char *key, const char *groups) {
    struct dn_span g = dn_before_guard(DN_RECOVER_AREA);
    unsigned char *a = g.data, *scan = a + DN_RECOVER_SCAN;
    memset(a, 0, DN_RECOVER_AREA);
    memcpy(a + DN_RECOVER_KEY, key, 16);
    uint64_t count = 0;
    if (strcmp(groups, "-")) {
        for (const char *p = groups; *p; ++count) {
            size_t len = strcspn(p, ","), n;
            if (count == DN_RECOVER_GROUPS_MAX) dn_harness("more groups than the configuration holds");
            unsigned char *name = unhex(p, len, &n), *group = a + DN_RECOVER_GROUPS + count * DN_RECOVER_GROUP_SLOT;
            if (n > DN_RECOVER_GROUP_SLOT - 8) dn_harness("a group name longer than the configuration holds");
            dn_put_word(group, n);
            memcpy(group + 8, name, n);
            free(name);
            p += len + (p[len] == ',');
        }
    }
    dn_put_word(a + DN_RECOVER_GROUP_COUNT, count);
    const struct entry *journal = lookup("journal", 7);
    static char actions[1 << 22], aside[1 << 20];
    size_t actions_len = 0, aside_len = 0, next_name = 0;
    said_len = 0;
    uint64_t bound = 64 + 4 * entries + (journal ? 4 * journal->len : 0);
    for (uint64_t steps = 0;; ++steps) {
        if (steps > bound) dn_violation("recovery took %" PRIu64 " steps", steps);
        uint32_t status = dn_recover_step((uintptr_t)a);
        if (status != dn_word(a + DN_RECOVER_STATUS))
            dn_violation("recovery returned %" PRIu32 ", its area says %" PRIu64, status,
                         dn_word(a + DN_RECOVER_STATUS));
        uint64_t seq = dn_word(a + DN_RECOVER_SEQ);
        if (status == DN_RECOVER_ASKS_NAME) {
            if (dn_word(a + DN_RECOVER_FIRST)) next_name = 0;
            dn_put_word(a + DN_RECOVER_END, next_name == entries);
            if (next_name < entries) {
                const struct entry *e = &dir[next_name++];
                if (e->name_len > DN_RECOVER_NAME_MAX) dn_harness("a name longer than a directory holds");
                dn_put_word(a + DN_RECOVER_NAME_LEN, e->name_len);
                memcpy(a + DN_RECOVER_NAME, e->name, e->name_len);
            }
        } else if (status == DN_RECOVER_ASKS_JOURNAL) {
            if (!journal) dn_violation("recovery asked for a journal the directory does not hold");
            dn_put_word(a + DN_RECOVER_JOURNAL_SIZE, journal->len);
        } else if (status == DN_RECOVER_ASKS_OCTETS) {
            uint64_t base = dn_word(scan + DN_SCAN_BASE), len = dn_word(scan + DN_SCAN_LEN);
            uint64_t want = dn_word(scan + DN_SCAN_WANT), n = journal ? journal->len : 0;
            if (!want || len > DN_SCAN_WINDOW_MAX - want || base > n || len > n - base || want > n - base - len)
                dn_violation("recovery asked for %" PRIu64 " octets of the journal after %" PRIu64, want, base + len);
            memcpy(scan + DN_SCAN_WINDOW + len, journal->data + base + len, want);
            dn_put_word(scan + DN_SCAN_LEN, len + want);
        } else if (status == DN_RECOVER_ASKS_FILE) {
            const struct entry *e = named('a', seq);
            dn_put_word(a + DN_RECOVER_FOUND, e != NULL);
            dn_put_word(a + DN_RECOVER_FILE_SIZE, e ? e->len : 0);
        } else if (status == DN_RECOVER_ASKS_ASIDE) {
            dn_put_word(a + DN_RECOVER_FOUND, named('q', seq) != NULL);
        } else if (status == DN_RECOVER_GIVES || status == DN_RECOVER_GIVES_ASIDE) {
            size_t mark = said_len;
            uint64_t x = dn_word(a + DN_RECOVER_ACT_A), y = dn_word(a + DN_RECOVER_ACT_B);
            if (status == DN_RECOVER_GIVES_ASIDE) {
                sayf("%" PRIu64, x);
            } else {
                switch (dn_word(a + DN_RECOVER_ACT)) {
                case DN_RECOVER_KEEP: {
                    uint64_t at = dn_word(a + DN_RECOVER_ACT_AT), len = dn_word(a + DN_RECOVER_ACT_LEN);
                    unsigned char kept[8 + DN_SCAN_WINDOW_MAX];
                    if (len > DN_SCAN_WINDOW_MAX) dn_violation("a tail of %" PRIu64 " octets", len);
                    for (int i = 0; i < 8; ++i) kept[i] = (unsigned char)(y >> (8 * i));
                    memcpy(kept + 8, in_area(a, at, len), len);
                    say("keep:", 5);
                    say_name('j', x);
                    say(":", 1);
                    say_hex(kept, 8 + len);
                    break;
                }
                case DN_RECOVER_RENAME:
                    say("rename:", 7);
                    say_name('a', x);
                    say(":", 1);
                    say_name('q', x);
                    break;
                case DN_RECOVER_REMOVE:
                    if (y != DN_RECOVER_NAME_FINAL && y != DN_RECOVER_NAME_TEMP)
                        dn_violation("a removal of kind %" PRIu64, y);
                    say("remove:", 7);
                    say_name(y == DN_RECOVER_NAME_FINAL ? 'a' : 't', x);
                    break;
                case DN_RECOVER_SYNC_DIR: say("sync-dir", 8); break;
                case DN_RECOVER_CUT: sayf("cut:%" PRIu64, x); break;
                case DN_RECOVER_CREATE:
                    say("create:", 7);
                    say_hex(key, 16);
                    break;
                default: dn_violation("an action of kind %" PRIu64, dn_word(a + DN_RECOVER_ACT));
                }
            }
            char *list = status == DN_RECOVER_GIVES ? actions : aside;
            size_t *list_len = status == DN_RECOVER_GIVES ? &actions_len : &aside_len;
            size_t n = said_len - mark;
            if (*list_len + n + 2 > (status == DN_RECOVER_GIVES ? sizeof actions : sizeof aside))
                dn_harness("more output than the host keeps");
            if (*list_len) list[(*list_len)++] = status == DN_RECOVER_GIVES ? ';' : ',';
            memcpy(list + *list_len, said + mark, n);
            *list_len += n;
            list[*list_len] = 0;
            said_len = mark;
        } else if (status == DN_RECOVER_DONE) {
            say("ok ", 3);
            say_hex(dn_word(a + DN_RECOVER_FRESH) ? key : scan + DN_SCAN_KEY, 16);
            sayf(" %" PRIu64 " %" PRIu64 " ", dn_word(a + DN_RECOVER_NEXT), dn_word(a + DN_RECOVER_JOURNAL_END));
            articles(a);
            say(" ", 1);
            say(aside_len ? aside : "-", aside_len ? aside_len : 1);
            say(" ", 1);
            say(actions_len ? actions : "-", actions_len ? actions_len : 1);
            break;
        } else if (status == DN_RECOVER_REFUSED) {
            fault(a);
            break;
        } else {
            dn_violation("recovery stopped with status %" PRIu32, status);
        }
    }
    dn_unmap(g);
}

int main(void) {
    dn_expect_faults();
    dn_runtime_init();
    static char line[1 << 24];
    uint64_t cases = 0;
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\n")] = 0;
        char *groups = strchr(line, ' '), *image = groups ? strchr(groups + 1, ' ') : NULL;
        char *want = image ? strchr(image + 1, ' ') : NULL;
        if (!want) dn_harness("a line without its groups, directory and answer");
        *groups++ = 0;
        *image++ = 0;
        *want++ = 0;
        size_t key_len;
        unsigned char *key = unhex(line, strlen(line), &key_len);
        if (key_len != 16) dn_harness("a key of %zu octets", key_len);
        entries = 0;
        if (strcmp(image, "-")) {
            for (char *p = image; *p;) {
                size_t len = strcspn(p, ";"), eq = strcspn(p, "=");
                if (eq >= len) dn_harness("a directory entry without its octets");
                if (entries == entries_cap) {
                    entries_cap = entries_cap ? 2 * entries_cap : 64;
                    dir = realloc(dir, entries_cap * sizeof *dir);
                    if (!dir) dn_harness("out of memory");
                }
                struct entry *e = &dir[entries++];
                e->name = unhex(p, eq, &e->name_len);
                e->data = unhex(p + eq + 1, len - eq - 1, &e->len);
                p += len + (p[len] == ';');
            }
        }
        recover(key, groups);
        if (strcmp(said, want)) dn_violation("recovery found %.300s, not %.300s", said, want);
        for (size_t i = 0; i < entries; ++i) free(dir[i].name), free(dir[i].data);
        free(key);
        ++cases;
    }
    printf("{\"recover_cases\": %" PRIu64 "}\n", cases);
    return 0;
}
