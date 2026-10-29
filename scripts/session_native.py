#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The session's program (`DN.Server.Session`), compiled, held against its model turn by turn.

The gate prints the program; CakeML compiles it without `--main_return`; `native/session_host.c`
runs it and speaks the line protocol of `dn-compiler session-model`, so the host simulator of
`scripts/session_check.py` drives the compiled code exactly as it drives the model. Every scenario
is run on both and the two traces — every batch, every action, what the host took, every next
turn — have to be the same, and with a store every job too: the compiled code recovers its store
first, from the spool before the start record the model's begins with. So do their whole answers to
each host that breaks the contract, to scripts at the edges of what it allows, and to hosts drawn at
random from a fixed seed. Hosts that break the contract in ways the model's protocol cannot say — an
identity that does not fit the replies, a configuration the store refuses, an event of no kind the
layout has, a word of the program's own area that the host overwrites — have to stop the compiled
code with their codes. The
host checks, on every call and at the end of the run, the heap header, and the heap before the
program's first area and past its layout, which it fills before the run so that the program cannot
lean on what it did not write.

Each defect planted in the printed program has to be caught, and caught the way it names.
"""
from __future__ import annotations

import argparse
from collections import Counter
from collections.abc import Iterator
import dataclasses
import os
from pathlib import Path
import random
import re
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lanes  # the path above is what makes these importable
from lanes import NATIVE, ROOT, LaneError, Report
import session_check as sessions
from session_check import GREETING, IDENTITY, LONGEST, SHORTEST, SOURCE, WALL, Identity, Speaker
import session_ref as ref
from session_ref import Turn
import store_ref as J

OUT = ROOT / "build/session"
HOST = NATIVE / "session_host.c"
HOSTS = [HOST, NATIVE / "session_calls.h", NATIVE / "call_checks.h", NATIVE / "cake_header.c", *lanes.RUNTIME]
LIMIT = 2 ** 62
# The hosts drawn at random: how many, how many turns each at most, and the seed.
RUNS, STEPS, SEED = 200, 60, 20_260_928

# Defects planted in the printed program: (name, a pattern, what it becomes, how many times, and
# what the message that catches it says). `{past}`, the first word past the layout, and `{stop}`,
# the word of the stop's code, are the layout's.
TRACE = "differs at turn"
# The defects planted in the store's side, which only the scenarios with a store can see.
POST_DEFECTS = [
    ("an article's dots not stuffed", r"if \(lds 1 \(zs \+ 80\)\) & \(b == 46\) \{", "if 0 {", 1, TRACE),
    ("an article one octet longer taken", r"1000000 < ar", "1000001 < ar", 2, TRACE),
    ("an article's deadline a millisecond late", r"st cb \+ 128, now \+ 1800000;", "st cb + 128, now + 1800001;", 1,
     TRACE),
    ("a commit's number the group's highest", r"(var num = \(lds 1 \(@base \+ \d+ \+ \(gx \* 8\)\)\)) \+ 1;", r"\1;", 1,
     TRACE),
    ("a file's CRC-32C begun at zero", r"st zs \+ 152, 4294967295;", "st zs + 152, 0;", 1, TRACE),
    ("POSTs that wait given slots out of their order", r"(?s)(fun postAdmits\(.*?)\(at < fr\)", r"\1(at <= fr)", 1,
     TRACE),
    ("connections that wait given reads out of their order", r"(?s)(fun readAdmits\(.*?)\(at < fr\)",
     r"\1(at <= fr)", 1, TRACE),
    ("a file's CRC-32C not compared", r"if \(\(acc \^ 4294967295\) == \(lds 1 \(rs \+ 160\)\)\) == 0 \{", "if 0 {", 1,
     TRACE),
    ("the empty line after the header section not looked for",
     r"if 0 < \(\(\(f \+ 1\) == h\) \+ \(f == \(h \+ 1\)\)\) \{", "if 0 {", 1, TRACE),
    ("a line that starts with one dot read as stuffed", r"if bol & \(x == 46\) \{", "if 0 {", 1, TRACE),
    ("no Xref given", r"st rs \+ 224, xo;", "st rs + 224, 0;", 2, TRACE),
    ("an Xref line folded an octet late", r"if 998 < \(wd \+ 1 \+ ll\) \{", "if 999 < (wd + 1 + ll) {", 1, TRACE),
    ("the header section taken as read an octet early", r"var known = \(h \+ 2\) <= gt;",
     "var known = (h + 1) <= gt;", 1, TRACE),
    ("the empty line's CR not given once the buffer starts past it", r"if fp == h \{", "if 0 {", 1,
     "code 10 on a host that kept the contract"),
    ("NEXT taken at the current article", r"\(mode == 2\) & \(x < num\)", "(mode == 2) & (x <= num)", 1,
     "scenario \"a group's articles walked\""),
    ("LAST taken at the current article", r"\(mode == 3\) & \(num < x\)", "(mode == 3) & (num <= x)", 1,
     "scenario \"a group's articles walked\""),
    ("an empty group's lowest number 0", r"(if gk == 0 \{\s*st @base \+ \d+, )1;", r"\g<1>0;", 1,
     "scenario 'an empty group'"),
    ("an article read by its number not made current", r"st cb \+ 168, rn;", "st cb + 168, lds 1 (cb + 168);", 1,
     "scenario \"a group's articles walked\""),
    ("a UTF-8 continuation octet unchecked", r"if 0 < \(\(cz < clo\) \+ \(chi < cz\)\) \{", "if 0 {", 2,
     "scenario 'group names and arguments'"),
    ("a ? taken in a group's name", r"\(64 <= cz\) & \(cz <= 90\)", "(63 <= cz) & (cz <= 90)", 2,
     "scenario \"every octet in a group's name\""),
    ("a lead octet past F4 taken", r"if \(241 <= cz\) & \(cz <= 243\) \{", "if (241 <= cz) & (cz <= 245) {", 2,
     "scenario \"every octet in a group's name\""),
    ("a range of one number taken as all after it", r"(lo = val;\s*)hi = val;", r"\g<1>hi = 2147483647;", 3,
     "scenario \"a group's articles listed\""),
    ("a LISTGROUP's numbers past the group's highest as it is selected",
     r"if \(lds 1 \(@base \+ \d+\)\) < lh \{", "if 0 {", 1, "scenario 'a group listed as an article is posted to it'"),
    ("a pattern of a wildmat matched as a prefix", r"if \(fl == 0\) & \(j == pe\) \{", "if fl == 0 {", 1,
     "scenario 'the groups listed'"),
    ("a negated pattern of a wildmat taken for one", r"res = neg == 0;", "res = 1;", 1, "scenario 'the groups listed'"),
    ("a part of a listing one octet longer", r"if \(o \+ ln\) <= 512 \{", "if (o + ln) <= 513 {", 1,
     "scenario 'long listings to a slow reader'"),
    ("a listing's terminating line put with no room left", r"if \(o \+ 3\) <= 512 \{", "if 1 {", 1,
     "scenario 'long listings to a slow reader'"),
    ("a group's status y once the store has stopped", r"var yn = 110;", "var yn = 121;", 1,
     "scenario 'forty groups listed to a slow reader as the store stops'"),
    ("DATE a day late", r"(?s)(fun dateText\(.*?var dy = )cv & 31;", r"\g<1>(cv & 31) + 1;", 1, "scenario 'dates'"),
    ("a century's February given a leap day", r"artDiv\(doe, 36524\)", "artDiv(doe, 36525)", 1,
     "scenario \"DATE at the calendar's edges\""),
    ("a listing's inactivity deadline not started again", r"(?s)(fun listPart\(.*?)st cb \+ 48, now \+ 1800000;",
     r"\1st cb + 48, 0;", 1, "scenario 'a listing to a reader that pauses'"),
    ("the sixty-fourth group never listed", r"(?s)(fun listActive\(.*?)while k < gc \{",
     r"\1while k < (gc - (gc == 64)) {", 1, "scenario 'sixty-four groups listed'"),
    ("a wildmat's continuation octet unchecked",
     r"(?s)(fun listClassify\(.*?)if 0 < \(\(cz < clo\) \+ \(chi < cz\)\) \{", r"\1if 0 {", 1,
     "scenario 'every octet in a wildmat'"),
    ("a second of 61 taken by NEWGROUPS", r"\) <= 60\);", ") <= 61);", 1, "scenario 'dates'"),
    ("MODE READER answered 200 once the store has stopped",
     r"if \(lds 1 \(cb \+ 104\)\) & \(lds 1 \(@base \+ \d+\)\) \{(\s*)r = 38;", r"if lds 1 (cb + 104) {\1r = 38;", 1,
     "scenario 'MODE READER once the store has stopped'"),
    ("READER left out of the capabilities", r"(if \(r == 1\) & \(lds 1 \(@base \+ \d+\)\) \{\s*)r = 40;", r"\1r = 1;",
     1, "scenario 'a client that may not post'"),
    ("the READER lines left out of POST's capabilities",
     r"(?s)(if t == 13 \{.*?)j = 0;\s+while j < 70 \{.*?\}\s+o = o \+ 70;", r"\1", 1,
     "scenario 'the capabilities and help, then a post'"),
    ("a colon taken for a digit of LISTGROUP's number", r"(?s)(if dn == 0 \{.*?ok = \(47 < cz\) & \()cz < 58\)",
     r"\1cz < 59)", 3, "scenario 'every octet in a range'"),
    ("a colon taken for a digit of a range's end",
     r"(var cz = ld8 \(blk \+ 40 \+ s2 \+ dp \+ 1 \+ jq\);\s+ok = \(47 < cz\) & \()cz < 58\)", r"\1cz < 59)", 2,
     "scenario 'every octet in a range'"),
    ("a colon taken for a digit of a range's start", r"(?s)(if dn == 1 \{.*?ok = \(47 < cz\) & \()cz < 58\)",
     r"\1cz < 59)", 3, "scenario 'every octet in a range'"),
    ("a range starting at the most article number refused", r"(?s)(if dn == 1 \{.*?ok = )val <= 2147483647;",
     r"\1val < 2147483647;", 3, "scenario 'every octet in a range'"),
    ("a colon taken for a digit of an article's number",
     (r"(ok = \(1 <= l1\) & \(l1 <= 16\);\s+val = 0;\s+jq = 0;\s+while ok & \(jq < l1\) \{\s+"
      r"var cz = ld8 \(blk \+ 40 \+ s1 \+ jq\);\s+ok = \(47 < cz\) & \()cz < 58\)"), r"\1cz < 59)", 2,
     "scenario \"every octet in an article's number\""),
    ("LISTGROUP's number of the most refused", r"(?s)(if dn == 0 \{.*?ok = )val <= 2147483647;", r"\1val < 2147483647;",
     3, "scenario 'every octet in a range'"),
    ("a lowest number of more than one digit written wrong",
     r"(st8 @base \+ \d+ \+ ln \+ nlq, 48 \+ \(nlt - \(\(\(nlt \* 3435973837\) )>>> 35", r"\1>>> 36", 1,
     "scenario 'marks of two digits and three'"),
    ("MODE's argument unchecked", r"(\s*)if eqk \{(\s*)r = 37;", r"\1if 1 {\2r = 37;", 1,
     "scenario 'every letter of a keyword changed, with a store'"),
    ("a TAB in a field kept", r"(if x == 9 \{\s+)cv = 32;", r"\1cv = 9;", 2, "scenario 'overview"),
    ("the SP after a field's colon kept", r"fd = 1;", "fd = 0;", 2, "scenario 'overview"),
    ("fields named with regard to case", r"\(\(x - \(32 \* \(\(96 < x\) & \(x < 123\)\)\)\) == ", "(x == ", 2,
     "scenario 'overview"),
    ("the dots before lines counted in :bytes",
     r"var byt = \(\(lds 1 \(rs \+ 152\)\) \+ \(lds 1 \(rs \+ 408\)\)\) - \(lds 1 \(rs \+ 328\)\);",
     "var byt = (lds 1 (rs + 152)) + (lds 1 (rs + 408));", 1, "scenario 'overview"),
    ("Xref's folds not counted in :bytes", r"xo \+ 2 \+ \(folds \* 2\);", "xo + 2;", 1, "scenario 'overview"),
    ("a range past the group's highest number then", r"(\n\s*)vup = lds 1 \(@base \+ \d+\);", r"\1skip;", 1,
     "scenario 'overview"),
    ("the dot line after every article", r"if \(lds 1 \(rs \+ 272\)\) == 0 \{", "if 1 {", 1, "scenario 'overview"),
    ("an article of an OVER made current", r"if \(\(gv == 0\) & \(0 < m\)\) & \(\(lds 1 \(rs \+ 240\)\) == 0\) \{",
     "if (gv == 0) & (0 < m) {", 1, "scenario 'overview"),
    ("a read failing after its first line answered 403",
     r"\(0 < \(\(\(lds 1 \(rs \+ 240\)\) == 0\) \+ \(lds 1 \(rs \+ 264\)\)\)\)", "1", 1, "scenario 'overview"),
    ("a header section past the buffer read", r"69632 < hd", "69633 < hd", 1, "scenario 'overview"),
    ("LISTGROUP passing over a commit after each number", r"ld = nd;", "ld = nd + 1;", 1,
     "scenario \"a group's articles listed\""),
    ("a LISTGROUP's cursor left where the last one ended", r"(st cb \+ 192, gnew - 1;\s+)st cb \+ 216, 0;", r"\1skip;",
     1, "scenario \"a group's articles listed\""),
    ("a name that is a prefix of a field's taken for it", r"\(nl == fn\)", "(fn <= nl)", 2, "scenario 'overview"),
    ("XHDR's line of a message-id numbered", r"if \(lds 1 \(rs \+ 248\)\) & \(lds 1 \(rs \+ 256\)\) \{", "if 0 {", 1,
     "scenario 'overview by message-id'"),
    ("HDR's :lines given as :bytes", r"hk = 2;", "hk = 1;", 1, "scenario 'fields of a range'"),
    ("the first line given before every article's", r"st rs \+ 264, 0;", "st rs + 264, 1;", 1, "scenario 'overview"),
    ("a header line's stuffed dot taken into its name", r"if \(b0 & \(x == 46\)\) == 0 \{", "if 1 {", 1,
     "scenario 'fields of a range'"),
    ("an XHDR line for an article without the field", r"if \(\(lds 1 \(rs \+ 248\)\) & \(vl == 0\)\) == 0 \{",
     "if 1 {", 1, "scenario 'overview"),
    ("the last field of a name taken", r"fo = fo \| \(", "fo = 0 * (", 2, "scenario 'fields of a range'"),
    ("the empty line counted among the body's", r"if \(\(h \+ 2\) <= f\) & \(x == 10\) \{",
     "if (h <= f) & (x == 10) {", 1, "scenario 'overview"),
]
DEFECTS = [
    ("the first command's deadline a second late", r"now \+ 10000;", "now + 11000;", 1, TRACE),
    ("an index opened again at its last generation", r"\(eg <= \(lds 1 \(cb \+ 8\)\)\)", "(eg < (lds 1 (cb + 8)))", 1,
     "breach 'an index opened again at its generation'"),
    ("a generation past its limit taken", r"\(4611686018427387904 < eg\)", "(4611686018427387905 < eg)", 1,
     "breach 'a generation past its limit'"),
    ("a line's deadline a millisecond late", r"now \+ 180000;", "now + 180001;", 2, TRACE),
    ("keywords compared with regard to case", r"\(32 \* \(\(96 <", "(0 * ((96 <", 37, TRACE),
    ("a prefix of READER taken by MODE", r"(if cmd == 16 \{\s+if args == 1 \{\s+eqk = )l1 == 6;", r"\1l1 <= 6;", 1,
     "scenario 'commands'"),
    ("READER compared with regard to case", r"(?s)(if cmd == 16 \{.*?)\(32 \* \(\(96 <", r"\1(0 * ((96 <", 1,
     "scenario 'MODE READER without a store'"),
    ("the first letter of a keyword not compared", r"jq = 0;(\s+)while eqk & \(jq < l", r"jq = 1;\1while eqk & (jq < l",
     30, "scenario 'every letter of a keyword changed'"),
    ("MODE READER's 502 without the close", r"if 0 < \(\(r == 3\) \+ \(r == 37\)\) \{", "if 0 < ((r == 3) + 0) {", 1,
     "scenario 'MODE READER without a store'"),
    ("an article number of any size", r"val <= 2147483647", "val <= 9999999999999999", 10, TRACE),
    ("a bare LF ending a command", r"if cr & \(bad == 0\) \{", "if bad == 0 {", 1, TRACE),
    ("an overlong line with no word left unanswered", r"if kind == 3 \{(\s*)r = 6;", r"if kind == 3 {\1r = 0;", 1,
     TRACE),
    ("a message-id of 251 bytes accepted", r"\(l1 <= 250\)", "(l1 <= 251)", 2, TRACE),
    ("a byte after Z taken for a letter inside a keyword",
     r"ok = 0 < \(\(0 < \(\(0 < \(\(\(64 < cz\) & \(cz < 91\)\)", "ok = 0 < ((0 < ((0 < (((64 < cz) & (cz < 92))",
     1, TRACE),
    ("output sent again before the host reports it ready", r"if \(lds 1 \(cb \+ 32\)\) == 0 \{", "if 1 {", 1, TRACE),
    ("lines after a QUIT answered", r"st cb \+ 16, 1;", "st cb + 16, 0;", 1, TRACE),
    ("output taken not counted as activity", r"(if \(0 < tk\) & .*\{\s*)st cb \+ 48, now \+ 1800000;",
     r"\1st cb + 48, lds 1 (cb + 48);", 1, TRACE),
    ("a send of which nothing was taken counted as activity", r"if \(0 < tk\) &", "if (0 <= tk) &", 1, TRACE),
    ("reading asked with a line held",
     r"var wants = \(\(\(lds 1 \(cb \+ 16\)\) == 0\) & \(\(lds 1 \(cb \+ 80\)\) == \(lds 1 \(cb \+ 72\)\)\)\) &",
     "var wants = ((lds 1 (cb + 16)) == 0) &", 1, TRACE),
    ("received bytes not held", r"st cb \+ 72, el;", "st cb + 72, 0;", 1, TRACE),
    ("input of a connection gone applied", r"(?s)(if ek == 2 \{.*?)if lv \{", r"\1if lds 1 cb {", 1,
     "code 4 on a host that kept the contract"),
    ("readiness of a connection gone applied", r"if ek == 3 \{(\s*)if lv \{", r"if ek == 3 {\1if lds 1 cb {", 1,
     TRACE),
    ("the end of input of a connection gone applied", r"if ek == 4 \{(\s*)if lv \{", r"if ek == 4 {\1if lds 1 cb {",
     1, "code 4 on a host that kept the contract"),
    ("the table not emptied at the start", r"while zt < 64 \{", "while zt < 0 {", 1,
     "code 6 on a host that kept the contract"),
    ("the longest revision refused", r"\(64 < rvl\)", "(63 < rvl)", 1, "code 9 on a host that kept the contract"),
    ("an identity with a space accepted", r"\(cz < 33\)", "(cz < 32)", 2, "not stop 9"),
    ("an event of an unknown kind accepted", r"\(5 < ek\)", "(6 < ek)", 1, "not stop 8"),
    ("a clock going back accepted", r"\(now < \(lds 1 \(@base \+ \d+\)\)\)", "(now < 0)", 1, "not stop 7"),
    ("a clock refused just below its limit", r"4611686018427387904 <= now", "4611686018427387903 <= now", 1,
     "at the edge 'a clock just below its limit'"),
    ("a word to read of two", r"st slot \+ 32, wants;", "st slot + 32, wants * 2;", 2, "word to read is 2"),
    ("a word to listen of two", r"st @base \+ {listen}, 1;", "st @base + {listen}, 2;", 2, "listening 2"),
    ("a store past the program's layout", r"st @base \+ \d+, now;", "st @base + {past}, now;", 1,
     "wrote past its layout"),
    ("a store before the program's first area", r"(st @base \+ {conf}, \d+;)", r"\1\n  st @base + 48, 7;", 1,
     "wrote before its layout"),
    ("a slot not cleared", r"\n\s*st @base \+ \d+ \+ \(c \* 560\), 0;", "", 1, "in the slots"),
    ("a send not counted", r"(aj = aj \+ 1;\s*\}\s*)st @base \+ {acts}, \(lds 1 \(@base \+ {acts}\)\) \+ 1;", r"\1", 1,
     "actions counted"),
    ("a length read back unchecked", r"\(512 < ol\)", "0", 1, "a send of 1000 bytes"),
    ("a store past the layout as the run stops", r"st @base \+ {stop}, 7;",
     "st @base + {past}, 1;\n      st @base + {stop}, 7;", 1, "the end of the run: the program wrote past its layout"),
]


def plant(source: str, pattern: str, becomes: str, times: int) -> str:
    return lanes.plant(source, pattern, becomes, times, "the program, for a planted defect,")


def first_difference(expected: list[Turn], got: list[Turn], broken: str | None) -> str | None:
    """Where a trace first differs from the model's: at a turn both have, else where it broke
    off, else in its length."""
    for k, (e, g) in enumerate(zip(expected, got, strict=False)):
        if e != g:
            if (g.actions, g.deadline) == (e.actions, e.deadline):
                return f"{TRACE} {k}, at {e.now}: jobs {g.jobs}, the model {e.jobs}"
            return f"{TRACE} {k}, at {e.now}: {g.actions} then {g.deadline}, the model {e.actions} then {e.deadline}"
    if broken:
        return broken
    if len(expected) != len(got):
        return f"{len(got)} turns, the model {len(expected)}"
    return None


def trace(clients: list[sessions.Client], command: list[str], ghosts: bool,
          identity: Identity) -> tuple[list[Turn], str | None]:
    """The turns of a scenario, and why it could not run to its end, if it could not."""
    try:
        return sessions.run(clients, command, ghosts, identity), None
    except sessions.Unfinished as error:
        return error.trace, str(error)


def edges() -> Iterator[tuple[str, list[str]]]:
    """Scripts at the edges of what the contract allows; each ends with the end of input, between
    turns."""
    begin = ["turn 1", "open 0 1", "go", f"took {GREETING}"]
    quit_, help_ = b"QUIT\r\n".hex(), b"HELP\r\n".hex()
    yield "a clock just below its limit", [f"turn {LIMIT - 1}", "open 0 1", "go", f"took {GREETING}",
                                           f"turn {LIMIT - 1}", "go", "took"]
    yield "a clock of zero", ["turn 0", "open 0 1", "go", "took 0", "turn 0", "go", "took"]
    below = sessions.WALL_LIMIT - 1
    yield "a wall clock just below its limit", [f"turn 1 {below}", "open 0 1", "go", f"took {GREETING}",
                                                f"turn 2 {below}", "go", "took"]
    yield "a batch of sixteen events", ["turn 1", *[f"open {k} 1" for k in range(16)], "go",
                                        "took " + " ".join([str(GREETING)] * 16)]
    yield "a chunk of 512 bytes", [*begin, "turn 2", "recv 0 1 " + (b"HELP\r\n" * 85 + b"ST").hex(), "go", "took 10"]
    yield "the last index", ["turn 1", "open 63 7", "go", f"took {GREETING}", "turn 2", f"recv 63 7 {help_}", "go",
                             "took 5"]
    yield "a generation at its limit", ["turn 1", f"open 0 {LIMIT}", "go", f"took {GREETING}", "turn 2",
                                        f"recv 0 {LIMIT} {help_}", "go", "took 5"]
    stale = ["writable 0 1", "end 0 1", "closed 0 1"]
    yield "events of a connection gone", [
        *begin, "turn 2", "closed 0 1", "go", "took", "turn 3", f"recv 0 1 {quit_}", *stale, "go", "took",
        "turn 4", "open 0 2", f"recv 0 1 {quit_}", *stale, "go", f"took {GREETING}",
        "turn 5", f"recv 0 2 {help_}", f"recv 0 1 {quit_}", *stale, "go", "took 3",
        "turn 6", "writable 0 1", "writable 0 2", "go", "took 0"]


def layout(out: Path = OUT) -> dict[str, int]:
    """The layout's constants, as the header in `out` the host is built with says them."""
    found = re.findall(r"#define DN_SESSION_(\w+) (\d+)", (out / "dn_session_layout.h").read_text())
    return {name: int(value) for name, value in found}


def own_area_written() -> Iterator[tuple[str, Identity, list[str], int]]:
    """Hosts that write into the program's own area a word it reads back as a length or a
    position, one for each place it checks such a word."""
    words = layout()
    own, record, slot = words["OWN_OFF"], words["TABLE_OFF"], words["CONN_SLOT"]
    greet, taken = ["turn 1", "open 0 1", "go", f"took {GREETING}"], ["turn 1", "open 0 1", "go", "took 10"]
    word, negative = 2 ** 64 - 1, 2 ** 63
    for what, script in [
        ("an output length", [*taken, "turn 2", f"poke {record + words['C_OUT_LEN']} 1000", "writable 0 1"]),
        ("a negative output length",
         [*taken, "turn 2", f"poke {record + words['C_OUT_LEN']} {negative}", "writable 0 1"]),
        ("an output length taken back", [*taken, "turn 2", f"poke {record + words['C_ACTED']} 1",
                                         f"poke {record + words['C_OUT_LEN']} 1000"]),
        ("the revision's length", ["turn 1", "go", "took", "turn 2", f"poke {own + words['OWN_REV_LEN']} 65",
                                   "open 0 1"]),
        ("a negative revision length", ["turn 1", "go", "took", "turn 2",
                                        f"poke {own + words['OWN_REV_LEN']} {word}", "open 0 1"]),
        ("the source's length", ["turn 1", "go", "took", "turn 2", f"poke {own + words['OWN_SRC_LEN']} 201",
                                 "open 0 1"]),
        ("a held length", [*greet, "turn 2", f"poke {record + words['C_HELD_LEN']} 1000"]),
        ("a held position", [*greet, "turn 2", f"poke {record + words['C_HELD_POS']} {word}"]),
        ("the framer's line length", [*greet, "turn 2", f"poke {record + words['C_FRAMER']} 513", "recv 0 1 41"]),
        ("a held length of the last connection",
         ["turn 1", "open 63 1", "go", f"took {GREETING}", "turn 2",
          f"poke {record + 63 * slot + words['C_HELD_LEN']} 1000"]),
    ]:
        yield f"{what} written by the host", IDENTITY, [*script, "go", "took"], 10


START = len(J.frame(sessions.KEY, 0, J.START, b""))


def native_line(spool: sessions.Spool) -> str:
    """The store line the compiled session is told: the spool before the start record its
    recovery appends, which the model's spool already ends with."""
    image = [(name, octets[:-START] if name == b"journal" else octets) for name, octets in spool.image]
    return dataclasses.replace(spool, image=image).line()


def store_area_written() -> Iterator[tuple[str, Identity, list[str], int]]:
    """Hosts with a store that write into the program's own area a word of the store's side it reads
    back as a length or a place."""
    words = layout()
    spool = sessions.Spool(sessions.GROUPS)
    slot0, record = words["SLOTS_OFF"], words["TABLE_OFF"]
    greeted = len(ref.texts(*IDENTITY)["greeting-post"])
    posting = [native_line(spool), f"turn 1 {WALL + 1}", "open 0 1 1", "go", f"took {greeted}",
               f"turn 5 {WALL + 5}", "recv 0 1 " + sessions.ascii_lines("POST").hex(), "go", "took 31",
               f"turn 6 {WALL + 6}"]
    article = "recv 0 1 " + sessions.article(*sessions.BASIC).hex()
    word = 2 ** 63
    yield "a slot's octets written by the host", IDENTITY, [
        *posting, f"poke {slot0 + words['Z_PEND']} {word}", article, "go", "took"], 10
    yield "the slot of a POST written by the host", IDENTITY, [
        *posting, f"poke {record + words['C_POST']} 9", article, "go", "took"], 10
    asking = [native_line(spool), f"turn 1 {WALL + 1}", "open 0 1 1", "go", f"took {greeted}", f"turn 5 {WALL + 5}"]
    for what, pokes, line in (
            ("the selected group", [(words["C_GROUP"], 65)], "STAT"),
            ("the current article", [(words["C_GROUP"], 1), (words["C_CURRENT"], word)], "NEXT"),
            ("the count of the store's groups", [(None, 65)], "GROUP local.test")):
        written = [f"poke {record + at if at is not None else words['REC_OFF'] + words['REC_GROUP_COUNT']} {value}"
                   for at, value in pokes]
        yield f"{what} written by the host", IDENTITY, [
            *asking, *written, "recv 0 1 " + sessions.ascii_lines(line).hex(), "go", "took"], 10
    selected = len(b"211 0 1 0 local.test\r\n")
    listing = [*asking, "recv 0 1 " + sessions.ascii_lines("LISTGROUP local.test").hex(), "go", f"took {selected}",
               f"turn 6 {WALL + 6}"]
    for what, at, value in (("the kind of a listing", "C_LIST", 3), ("the group of a listing", "C_LIST_A", 65)):
        yield f"{what} written by the host", IDENTITY, [
            *listing, f"poke {record + words[at]} {value}", "go", "took"], 10
    yield "the count of POSTs that wait written by the host", IDENTITY, [
        native_line(spool), f"turn 1 {WALL + 1}", "open 0 1 1", "go", f"took {greeted}", f"turn 5 {WALL + 5}",
        f"poke {words['OWN_OFF'] + words['OWN_WAIT_N']} 65", "recv 0 1 " + sessions.ascii_lines("POST").hex(),
        "go", "took"], 10
    yield "the index written by the host", IDENTITY, [
        *posting, *(f"poke {words['INDEX_OFF'] + 8 * k} {word}" for k in range(words["INDEX_CELLS"])), article,
        "go", "took"], 10
    for what, change in (("a path identity that is no domain name", {"identity": b"dn example"}),
                         ("a group the store may not carry", {"groups": [b"local..test"]})):
        yield f"{what}", IDENTITY, [native_line(dataclasses.replace(spool, **change)), f"turn 1 {WALL}", "go",
                                    "took"], 9


def program_breaches() -> Iterator[tuple[str, Identity, list[str], int]]:
    """Hosts that break the contract in ways only the program is asked to see, and their codes."""
    first = ["turn 1", "go", "took"]
    yield from own_area_written()
    yield from store_area_written()
    yield "no identity", (b"", b""), first, 9
    yield "no revision", (b"", SOURCE), first, 9
    yield "no address of the source", (b"r", b""), first, 9
    yield "a revision one byte too long", (b"r" * 65, SOURCE), first, 9
    yield "an address one byte too long", (b"r", b"s" * 201), first, 9
    yield "a space in the revision", (b"0123 abc", SOURCE), first, 9
    yield "a DEL in the address", (b"r", b"https://x\x7f"), first, 9
    for kind in (0, 6, 2 ** 63):
        yield f"an event of kind {kind}", IDENTITY, ["turn 1", f"raw {kind} 0 1", "go", "took"], 8


PIECES = (b"HELP", b"help", b"QUIT", b"CAPABILITIES", b"HEAD", b"STAT", b"LIST", b" ", b"\t", b"\r", b"\n",
          b"\r\n", b"\r\n", b"\r\n", b"<a@b>", b"<>", b"123", b"2147483648", b"x", b"\0", b"a-b.c", b".")
QUIT = b"QUIT\r\n".hex()


class Wander:
    """A host drawn at random: it mostly keeps the contract, as far as it can tell what the session
    asked for, and now and then breaks it. The model and the compiled code are told the same and
    have to answer the same."""

    def __init__(self, rng: random.Random, binary: Path) -> None:
        self.rng = rng
        identity = rng.choice([IDENTITY, LONGEST, SHORTEST])
        model = Speaker(sessions.model_command(), identity)
        try:
            self.pair = [model, Speaker([str(binary)], identity)]
        except BaseException:
            model.__exit__()
            raise
        self.gens = [0] * 64
        # each open connection: its generation, whether it asked for input, whether output is untaken
        self.live: dict[int, list[int]] = {}
        self.gone: list[tuple[int, int]] = []
        self.now = rng.choice([0, 1, 5, LIMIT - 10 ** 7])
        self.wake = 0

    def both(self, lines: list[str], ends: tuple[str, ...]) -> list[list[str]]:
        answers = []
        for session in self.pair:
            for line in lines:
                session.say(line)
            got = [session.hear()]
            while got[-1][0] not in ends:
                got.append(session.hear())
            answers.append(got)
        if answers[0] != answers[1]:
            raise LaneError(f"the compiled session answered {answers[1][-3:]}, the model {answers[0][-3:]}")
        return answers[0]

    def events(self) -> list[str]:
        rng, out, fed = self.rng, [], set()
        for _ in range(rng.choice([0, 1, 1, 2, 3, 16])):
            pick = rng.random()
            free = sorted(set(range(64)) - set(self.live))
            asked = [i for i, c in self.live.items() if c[1] and i not in fed]
            if pick < 0.25 and free:
                idx = free[0] if rng.random() < 0.8 else rng.choice(free)
                self.gens[idx] += 1
                self.live[idx] = [self.gens[idx], 0, 0]
                out.append(f"open {idx} {self.gens[idx]}")
            elif pick < 0.65 and asked:
                idx = rng.choice(asked)
                fed.add(idx)
                data = b"".join(rng.choice(PIECES) for _ in range(rng.randint(1, 8)))
                out.append(f"recv {idx} {self.live[idx][0]} {data.hex()}")
            elif pick < 0.8 and any(c[2] for c in self.live.values()):
                idx = rng.choice([i for i, c in self.live.items() if c[2]])
                self.live[idx][2] = 0
                out.append(f"writable {idx} {self.live[idx][0]}")
            elif pick < 0.85 and asked:
                idx = rng.choice(asked)
                fed.add(idx)
                self.live[idx][1] = 0
                out.append(f"end {idx} {self.live[idx][0]}")
            elif pick < 0.9 and self.live:
                idx = rng.choice(sorted(self.live))
                self.gone.append((idx, self.live.pop(idx)[0]))
                out.append(f"closed {idx} {self.gone[-1][1]}")
            elif self.gone:
                idx, gen = rng.choice(self.gone)
                out.append(rng.choice([f"recv {idx} {gen} {QUIT}", f"writable {idx} {gen}", f"end {idx} {gen}",
                                       f"closed {idx} {gen}"]))
        return out

    def breach(self) -> list[str]:
        choices = [[f"open {k} 9" for k in range(17)], [f"open 64 {self.gens[0] + 1}"], ["recv 0 1 " + "41" * 513]]
        choices += [[f"open {idx} {c[0] + 1}"] for idx, c in self.live.items()]
        choices += [[f"recv {idx} {c[0]} 41"] for idx, c in self.live.items() if not c[1]]
        return self.rng.choice(choices)

    def run(self, steps: int) -> tuple[int, int | None]:
        """How many turns the host ran, and the code the session stopped with, if it stopped."""
        rng = self.rng
        for step in range(steps):
            if rng.random() < 0.2 and self.wake:
                self.now = max(self.now, self.wake + rng.choice([-1, 0, 0, 1]))
            else:
                self.now += rng.choice([0, 1, 3, 1000, 9999, 10000, 180000, 1800000])
            now = self.now - 1 if rng.random() < 0.005 and self.now else self.now
            lines = self.events() + (self.breach() if rng.random() < 0.01 else [])
            answer = self.both([f"turn {now}", *lines, "go"], ("done", "stop"))
            if answer[-1][0] == "stop":
                return step + 1, int(answer[-1][1])
            took = self.settle(answer[:-1])
            if rng.random() < 0.005:
                took.append(1)
            end = self.both(["took " + " ".join(map(str, took))], ("deadline", "stop"))[-1]
            if end[0] == "stop":
                return step + 1, int(end[1])
            self.wake = int(end[1])
        return steps, None

    def settle(self, actions: list[list[str]]) -> list[int]:
        """What the kernel takes of each send, and what the host learns of each connection."""
        took = []
        for words in actions:
            idx = int(words[1])
            if words[0] != "send":
                self.gone.append((idx, self.live.pop(idx)[0]))
                continue
            size = 0 if words[3] == "-" else len(words[3]) // 2
            k = self.rng.choice([size, size, size, 0, self.rng.randint(0, size)])
            k += self.rng.random() < 0.005
            took.append(k)
            self.live[idx][1:] = [int(words[4] == "1" and k >= size), int(k < size)]
        return took

    def close(self) -> None:
        for session in self.pair:
            session.__exit__()


def wander(binary: Path, runs: int) -> dict[str, int]:
    """Runs of hosts drawn at random, the same for every program: how many turns, and how each
    ended."""
    rng = random.Random(SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same hosts
    seen: Counter[str] = Counter()
    for run in range(runs):
        host = Wander(rng, binary)
        try:
            steps, code = host.run(STEPS)
        except LaneError as error:
            raise LaneError(f"random host {run} of seed {SEED}: {error}") from None
        finally:
            host.close()
        seen["runs"] += 1
        seen["turns"] += steps
        seen["unstopped" if code is None else f"stop {code}"] += 1
    return dict(seen)


def scenarios_hold(binary: Path, scenarios: list[sessions.Scenario], expected: dict[str, list[Turn]]) -> None:
    for name, clients, ghosts, identity in scenarios:
        native, broken = trace(clients, [str(binary)], ghosts, identity)
        problem = first_difference(expected[name], native, broken)
        if problem:
            raise LaneError(f"scenario {name!r}: {problem}")


# Scenarios the compiled session also runs from an empty directory, its recovery making the journal
# the model's spool begins with.
FROM_EMPTY = ("a post",)


def posts_hold(binary: Path, posts: list[sessions.PostScenario], expected: dict[str, list[Turn]]) -> None:
    runs = [(name, clients, spool, native_line(spool)) for name, clients, spool in posts]
    runs += [(f"{name}, from an empty directory", clients, spool, dataclasses.replace(spool, image=[]).line())
             for name, clients, spool in posts if name in FROM_EMPTY]
    for name, clients, spool, line in runs:
        try:
            native, broken = sessions.run_post(clients, spool, [str(binary)], line), None
        except sessions.Unfinished as error:
            native, broken = error.trace, str(error)
        problem = first_difference(expected[name.removesuffix(", from an empty directory")], native, broken)
        if problem:
            raise LaneError(f"scenario {name!r}: {problem}")


# Breaches with a store the layout cannot hold: more completions than its slots, results for
# operations not done, and octets of a read other than its result counts, a job's data always being
# there; the model's lane has them.
UNWRITTEN = ("more completions than jobs", "results for operations not done", "octets a read does not count")


def post_breaches() -> Iterator[tuple[str, list[str], int]]:
    """The breaches with a store the layout can hold, told the compiled session's store line."""
    spools = (sessions.Spool(sessions.GROUPS), sessions.Spool(sessions.GROUPS, image=sessions.TWO))
    for name, script, code in (*sessions.post_breaches(), *sessions.read_breaches()):
        if name not in UNWRITTEN:
            lines = {spool.line(): native_line(spool) for spool in spools}
            yield name, [lines.get(line, line) for line in script], code


def scripts_hold(binary: Path, answers: dict[str, list[str]]) -> None:
    for name, script, code in (*sessions.breaches(), *post_breaches()):
        out, ended = sessions.breach_output(script, [str(binary)])
        if ended or out != answers[name]:
            raise LaneError(f"breach {name!r}: the compiled session answered {out[-3:]}{ended}, "
                            f"not stop {code} as the model")
    for name, identity, script, code in program_breaches():
        try:
            sessions.check_breach(script, code, [str(binary)], identity)
        except LaneError as error:
            raise LaneError(f"breach {name!r}: {error}") from None
    for name, script in edges():
        out, ended = sessions.breach_output(script, [str(binary)])
        if ended or out != answers[name]:
            raise LaneError(f"at the edge {name!r}: the compiled session answered {out[-4:]}{ended}, "
                            f"the model {answers[name][-4:]}")


def edge_answers(model: list[str]) -> dict[str, list[str]]:
    """The model's answers to the scripts at the edges, each of which it has to take to its end."""
    answers = {}
    for name, script in edges():
        out, ended = sessions.breach_output(script, model)
        if ended:
            raise LaneError(f"at the edge {name!r}: the model answered {out[-3:]}{ended}")
        answers[name] = out
    return answers


def check(cake: str) -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "dn_session_layout.h").write_text(lanes.emit("emit-session-layout"))
    source = lanes.emit("emit-session")
    words = layout()
    places = {"{past}": str(words["SIZE"]), "{stop}": str(words["OWN_OFF"] + words["OWN_STOP"]),
              "{listen}": str(words["EMIT_OFF"] + words["EMIT_LISTEN"]), "{conf}": str(words["CONF_OFF"]),
              "{acts}": str(words["OWN_OFF"] + words["OWN_ACTS"])}

    def placed(text: str) -> str:
        for place, offset in places.items():
            text = text.replace(place, offset)
        return text

    defects = DEFECTS + POST_DEFECTS
    clock = time.monotonic()
    seconds: dict[str, float] = {}
    # The program and each defect are built at once, while the model answers the hosts.
    with lanes.pool() as pool:
        built = pool.submit(lanes.whole_program, cake, "session", source, OUT, HOST)
        builds = [pool.submit(lanes.whole_program, cake, f"defect-{index}",
                              plant(source, placed(pattern), placed(becomes), times), OUT, HOST)
                  for index, (_, pattern, becomes, times, _) in enumerate(defects)]
        scenarios = list(sessions.scenarios())
        posts = [*sessions.post_scenarios(), *sessions.read_scenarios(), *sessions.abandon_scenarios(),
                 *sessions.group_scenarios(),
                 *sessions.list_scenarios(), *sessions.mode_scenarios(), *sessions.over_scenarios()]
        model = sessions.model_command()
        scripts = [(name, script, code) for name, script, code in
                   (*sessions.breaches(), *sessions.post_breaches(), *sessions.read_breaches())
                   if name not in UNWRITTEN]
        # The model runs as a process for each scenario, in parallel; then the program on each kind of
        # host at once. Each is taken in this order, and a difference told in it.
        with sessions.runs() as runs:
            plain = [runs.submit(sessions.run, clients, model, ghosts, identity)
                     for _, clients, ghosts, identity in scenarios]
            with_store = [runs.submit(sessions.run_post, clients, spool, model) for _, clients, spool in posts]
            answered = [runs.submit(sessions.check_breach, script, code, model) for _, script, code in scripts]
            edged = runs.submit(edge_answers, model)
            expected = {name: played.result() for (name, *_), played in zip(scenarios, plain, strict=True)}
            stored = {name: played.result() for (name, *_), played in zip(posts, with_store, strict=True)}
            answers = {name: answer.result() for (name, *_), answer in zip(scripts, answered, strict=True)}
            answers |= edged.result()
            seconds["model"] = round(time.monotonic() - clock, 1)
            binary = built.result()
            held = [runs.submit(scenarios_hold, binary, scenarios, expected),
                    runs.submit(posts_hold, binary, posts, stored), runs.submit(scripts_hold, binary, answers)]
            wandered = runs.submit(wander, binary, RUNS)
            for each in held:
                each.result()
            random_hosts = wandered.result()
        seconds["program"] = round(time.monotonic() - clock - seconds["model"], 1)

        def judged(index: int, name: str, sign: str) -> tuple[str, str]:
            """The program with the defect run as the program is, a defect of the store's side on the
            scenarios with a store first; how it was caught."""
            planted = builds[index].result()
            try:
                if index >= len(DEFECTS):
                    posts_hold(planted, posts, stored)
                scenarios_hold(planted, scenarios, expected)
                scripts_hold(planted, answers)
                posts_hold(planted, posts, stored)
                wander(planted, RUNS)
            except LaneError as error:
                if sign not in str(error):
                    raise LaneError(f"the program with {name} was caught, but not as {sign!r}: {error}") from None
                return name, str(error)[:400]
            raise LaneError(f"the program with {name} answered every host as the model")

        # Each defect is built and run apart from the others, judged by no clock.
        caught = dict(pool.map(lambda d: judged(d[0], d[1][0], d[1][4]), enumerate(defects)))
    seconds["defects"] = round(time.monotonic() - clock - seconds["model"] - seconds["program"], 1)
    turns = sum(len(t) for t in expected.values())
    store_turns = sum(len(t) for t in stored.values())
    lanes.require_quoted({"docs/baseline.md": [f"on the model's {len(scenarios)} scenarios and {turns:,} turns",
                                               f"{len(posts)} with a store and {store_turns:,} turns",
                                               f"{RUNS} hosts drawn at random"]})
    return Report("checked", cake, HOSTS, {
        "source_sha256": lanes.digest(OUT / "session.pnk"), "executable_sha256": lanes.digest(binary),
        "layout_sha256": lanes.digest(OUT / "dn_session_layout.h"), "scenarios": len(scenarios), "turns": turns,
        "store_scenarios": len(posts), "store_turns": store_turns,
        "breaches": sum(1 for _ in sessions.breaches()) + sum(1 for _ in post_breaches()),
        "program_breaches": sum(1 for _ in program_breaches()),
        "edges": sum(1 for _ in edges()), "random_hosts": random_hosts, "random_seed": SEED,
        "planted_defects_caught": caught, "seconds_by_step": seconds})


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cake", default=os.environ.get("CAKE"))
    args = parser.parse_args()
    lanes.require_platform(parser)
    cake = lanes.given_cake(parser, args.cake)
    lanes.lane_main("SESSION", OUT, lambda: check(cake))


if __name__ == "__main__":
    main()
