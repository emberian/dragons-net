#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The store lane: how the store recovers when it starts (`DN.News.Recovery`), as decision 0005
("On disk") fixes it, answered by `dn-compiler recovery-model` and by the independent
scripts/recovery_ref.py, which have to give the same answer, to the byte, on every case:

- a table of directories after the one `fn` keeps for its own store, each with the answer 0005
  gives it: every corruption 0005 lists, at its boundary and beside it — a name of no shape the
  store gives, files and no journal, a journal that does not read back or holds a frame of no
  record, a sequence number in two records, an article number not above the group's last, a group
  the configuration lacks, a file missing or of another size, no sequence number left — and a key
  not of sixteen octets, which the configuration refuses; which is reported when several hold, of
  one kind and of several; and the directories that recover — empty, a journal alone, a format cut
  short or filled with zeros alone, commits and starts and their files, crossposts and a last
  record whole but not answered, a torn commit, a torn start or zeros after the records, kept and
  cut, temporary files, final files no record names removed or set aside, files set aside before,
  tails kept below and above a final file;
- directories drawn at random from a fixed seed, with starts among their records and some breaking
  a rule across records, and the same damaged at random;
- actions drawn at random done on small directories (`apply`), names taken and not;
- for every directory that recovers, its actions done (`apply`) and recovery run on what they
  leave, on which both have to agree too: the same key, articles, end of the journal and files set
  aside, a next number no higher (a file removed frees its number), and nothing more to do.

Lines no case may be both have to refuse. Every way recovery can find a store corrupt has to be
seen, each version of recovery with one rule changed (`DN.News.RecoveryMutant`) has to answer some
case otherwise, and the documents have to state the numbers measured wherever they state them
(docs/baseline.md, "Store").
"""
from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
import random
import re
import struct
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import abnf_check as C  # the path above is what makes these importable
import journal_check as J
import lanes
from lanes import LaneError, Report

OUT = lanes.ROOT / "build/store"
REFERENCE = lanes.ROOT / "scripts/recovery_ref.py"
REQUIREMENTS = lanes.ROOT / "scripts/requirements-tests.txt"
SEED = 20261003
KEY = J.KEY
OTHER_KEY = bytes(range(16, 32))
GROUPS = [b"local.test", b"local.more"]
LIMIT = 2**64
# The versions of recovery with one rule changed, by the name `dn-compiler recovery-model --mutant`
# takes.
MUTANTS = ["seq-unchecked", "numbers-unchecked", "numbers-equal", "groups-unchecked", "size-unchecked",
           "missing-unchecked", "names-ignored", "journal-among-files", "remade-among-files",
           "next-records-only", "torn-no-bump", "tail-dropped", "tidy-first", "aside-never",
           "aside-always", "aside-at-tail", "temp-kept", "tidy-unsynced", "exhausted-late",
           "key-unchecked", "tail-unprefixed", "aside-over-quarantine", "key-from-config"]
# Why recovery finds a store corrupt, as both print it.
FAULTS = ["bad-name", "no-journal", "journal", "seq-twice", "number-not-above", "unknown-group",
          "missing-file", "wrong-size", "exhausted", "bad-key"]
# Lines both have to refuse to answer.
REFUSED = ["recover", "recover - - - -", "recover 0g - -", "recover - local -", "recover - 6a,,6b -",
           "recover - - 6a", "recover - - 6a=00;6a=01", "recover - - 6a=00;", "recover - - 6A=00",
           "apply - cut:x", "apply - create:00", "apply - frobnicate", "apply - keep:6a", "apply -",
           "apply - -;sync-dir", " ", "\t", "\r", "recover - - -\r", "scan 00"]

Files = list[tuple[bytes, bytes]]


@dataclass(frozen=True)
class Case:
    """A line to answer and, when the lane knows it, the answer."""
    line: str
    want: str | None = None

    def holds(self, said: str) -> bool:
        return self.want is None or said == self.want


def named(letter: str, seq: int) -> bytes:
    return letter.encode() + b"%016x" % seq


def hexed(data: bytes) -> str:
    return data.hex() or "-"


def image(files: Files) -> str:
    return ";".join(f"{hexed(n)}={hexed(d)}" for n, d in files) or "-"


def recover_line(files: Files, *, key: bytes = KEY, groups: list[bytes] | None = None) -> str:
    gs = GROUPS if groups is None else groups
    return f"recover {hexed(key)} {','.join(g.hex() for g in gs) or '-'} {image(files)}"


def ok(key: bytes, nxt: int, end: int, commits: Sequence[J.Commit], aside: list[int],
       actions: list[str]) -> str:
    """What both print of a store recovery starts with."""
    return (f"ok {key.hex()} {nxt} {end} {';'.join(map(J.shown, commits)) or '-'} "
            f"{','.join(map(str, aside)) or '-'} {';'.join(actions) or '-'}")


def corrupt(why: str) -> str:
    return f"corrupt {why}"


def commit(seq: int, number: int = 1, *, group: bytes = b"local.test", size: int = 1,
           more: tuple[tuple[bytes, int], ...] = ()) -> J.Commit:
    """A commit a correct store writes: its article `number` in `group`, and `more` groups."""
    return (seq, b"<%d@x>" % seq, ((group, number), *more), 0, size, 0)


def commits_of(items: Sequence[J.Item]) -> list[J.Commit]:
    return [i for i in items if not isinstance(i, str)]


def sizes(cs: Sequence[J.Commit]) -> dict[int, int]:
    """The size of each number's file, as the first commit of the number gives it."""
    out: dict[int, int] = {}
    for c in cs:
        out.setdefault(c[0], c[4])
    return out


def store(items: Sequence[J.Item], *, key: bytes = KEY) -> tuple[bytes, Files]:
    """A journal of `items`, commits and starts, and a file of the size each number gives under its
    final name."""
    j = J.journal(key, list(items))
    return j, [(b"journal", j), *((named("a", s), bytes(n)) for s, n in sizes(commits_of(items)).items())]


def kept(content: bytes, cut: int) -> str:
    return (struct.pack("<Q", cut) + content[cut:]).hex()


def keep_and_cut(content: bytes, cut: int, seq: int) -> list[str]:
    """The actions that keep the journal's octets from `cut` under the number `seq`, then cut it."""
    return [f"keep:{named('j', seq).hex()}:{kept(content, cut)}", "sync-dir", f"cut:{cut}"]


def torn_after(key: bytes, j: bytes, item: J.Item, n: int) -> bytes:
    """`j` and the first `n` octets of the frame `item` would get after it."""
    return j + J.encoded(key, len(j), item)[:n]


def table() -> list[Case]:
    """The directories decision 0005 sets out, each with the answer it gives them."""
    first = J.FIRST_FRAME
    fmt = J.format_frame(KEY)
    start = J.START_RECORD
    more, test = b"local.more", b"local.test"
    out: list[Case] = []

    def case(files: Files, want: str, *, key: bytes = KEY, groups: list[bytes] | None = None) -> None:
        out.append(Case(recover_line(files, key=key, groups=groups), want))

    # Empty, a journal alone, a format cut short or filled with zeros, alone or beside another file.
    case([], ok(KEY, 1, first, [], [], [f"create:{KEY.hex()}", "sync-dir"]))
    case([(b"journal", fmt)], ok(KEY, 1, first, [], [], []))
    for n in (0, 1, J.HEADER - 1, J.HEADER, first - 1):
        case([(b"journal", fmt[:n])], ok(KEY, 1, first, [], [], [f"create:{KEY.hex()}"]))
        case([(b"journal", fmt[:n]), (named("t", 1), b"")], corrupt("no-journal"))
    for n in (0, J.HEADER, first - 1):
        case([(b"journal", fmt[:n] + bytes(first - n))], ok(KEY, 1, first, [], [], [f"create:{KEY.hex()}"]))
    case([(b"journal", fmt)], ok(KEY, 1, first, [], [], []), key=OTHER_KEY)
    case([], ok(OTHER_KEY, 1, first, [], [], [f"create:{OTHER_KEY.hex()}", "sync-dir"]), key=OTHER_KEY)
    # Files and no journal.
    for letter in "atqj":
        case([(named(letter, 1), b"")], corrupt("no-journal"))
    # Names of no shape the store gives, the first in the listing.
    for other in (b"x", b"", b"journals", b"Journal", b"a" + b"0" * 15, b"a" + b"0" * 17, b"A" + b"0" * 16,
                  b"a" + b"0" * 15 + b"A", b"a" + b"0" * 15 + b"g", b"b" + b"0" * 16, b"journal\n",
                  named("a", 1) + b".tmp", b"./journal"):
        case([(b"journal", fmt), (other, b"")], corrupt(f"bad-name {hexed(other)}"))
    case([(b"y", b""), (b"x", b"")], corrupt(f"bad-name {b'y'.hex()}"))
    # A key that is not sixteen octets, whatever the directory.
    for k in (b"", KEY[:15], KEY + b"\x00"):
        case([], corrupt("bad-key"), key=k)
        case([(b"journal", fmt)], corrupt("bad-key"), key=k)
    # Commits and their files, and starts, which hold no article.
    for n in range(1, 4):
        cs = [commit(s, s) for s in range(1, n + 1)]
        j, files = store(cs)
        case(files, ok(KEY, n + 1, len(j), cs, [], []))
    cs = [commit(1, 7, more=((more, 3),)), commit(5, 8), commit(9, 4, group=more)]
    j, files = store(cs)
    case(files, ok(KEY, 10, len(j), cs, [], []))
    for items in ([start], [start, commit(1, 1), start, commit(2, 2), start]):
        j, files = store(items)
        case(files, ok(KEY, len(commits_of(items)) + 1, len(j), commits_of(items), [], []))
    # A sequence number in two records: the first that a later one repeats.
    for seqs in ([1, 1], [1, 2, 1], [3, 2, 3], [2, 2, 2], [1, 2, 2, 1]):
        cs = [commit(s, k + 1) for k, s in enumerate(seqs)]
        j, files = store(cs)
        dup = next(s for k, s in enumerate(seqs) if s in seqs[k + 1:])
        case(files, corrupt(f"seq-twice {dup}"))
    # An article number not above the group's last: the first record's, its first group's.
    for numbers, low in (([1, 1], 1), ([2, 1], 1), ([5, 6, 6], 6), ([1, 2, 1], 1)):
        cs = [commit(k + 1, number) for k, number in enumerate(numbers)]
        j, files = store(cs)
        case(files, corrupt(f"number-not-above {test.hex()} {low}"))
    cs = [commit(1, 1, more=((more, 4),)), commit(2, 2, more=((more, 4),))]
    j, files = store(cs)
    case(files, corrupt(f"number-not-above {more.hex()} 4"))
    cs = [commit(1, 5, more=((more, 5),)), commit(2, 1, group=more, more=((test, 1),))]
    j, files = store(cs)
    case(files, corrupt(f"number-not-above {more.hex()} 1"))
    cs = [commit(1, 1, more=((more, 4),)), commit(2, 5, group=more, more=((test, 2),))]
    j, files = store(cs)
    case(files, ok(KEY, 3, len(j), cs, [], []))
    # A group the configuration lacks: the first in the journal.
    for cs, lacked in (([commit(1, 1, group=b"other")], b"other"),
                       ([commit(1, 1), commit(2, 1, group=b"other")], b"other"),
                       ([commit(1, 1, more=((b"local.zzz", 1),))], b"local.zzz"),
                       ([commit(1, 1, more=((b"zz", 1),)), commit(2, 1, group=b"other")], b"zz")):
        j, files = store(cs)
        case(files, corrupt(f"unknown-group {lacked.hex()}"))
    j, files = store([commit(1, 1)])
    case(files, corrupt(f"unknown-group {test.hex()}"), groups=[more])
    case(files, corrupt(f"unknown-group {test.hex()}"), groups=[])
    # A file missing or of another size: the first record's.
    j, files = store([commit(1, 1), commit(2, 2)])
    case(files[:2], corrupt("missing-file 2"))
    case([files[0], files[2]], corrupt("missing-file 1"))
    for size in (0, 2):
        case([files[0], files[1], (named("a", 2), bytes(size))], corrupt("wrong-size 2"))
    case([files[0], (named("a", 1), bytes(2))], corrupt("wrong-size 1"))
    case([files[0], (named("q", 1), b"\x00"), files[2]], corrupt("missing-file 1"))
    # Which wins when several kinds hold: two records, then article numbers, then groups, then
    # files.
    cs = [commit(1, 2, group=b"other"), commit(1, 1)]
    j, _ = store(cs)
    case([(b"journal", j)], corrupt("seq-twice 1"))
    cs = [commit(1, 2), commit(2, 1, group=b"other", more=((test, 1),))]
    j, _ = store(cs)
    case([(b"journal", j)], corrupt(f"number-not-above {test.hex()} 1"))
    j, _ = store([commit(1, 1, group=b"other")])
    case([(b"journal", j)], corrupt(f"unknown-group {b'other'.hex()}"))
    case([(b"journal", j), (b"x", b"")], corrupt(f"bad-name {b'x'.hex()}"))
    # A journal that does not read back.
    j, files = store([commit(1, 1), commit(2, 2)])
    changed = bytearray(j)
    changed[len(fmt) + 20] ^= 1
    case([(b"journal", bytes(changed)), *files[1:]], corrupt(f"journal {len(fmt)} tag"))
    again = j + J.frame(KEY, len(j), J.FORMAT, J.MAGIC + KEY)
    case([(b"journal", again), *files[1:]], corrupt(f"journal {len(j)} format-again"))
    # A frame that checks but holds no record a correct store writes: of no type the format has, a
    # commit that does not decode, a format of another version.
    for kind, body in ((4, b""), (J.COMMIT, b"\x00")):
        bad = j + J.frame(KEY, len(j), kind, body)
        case([(b"journal", bad), *files[1:]], corrupt(f"journal {len(j)} not-a-record"))
    case([(b"journal", J.frame(KEY, 0, J.FORMAT, J.TITLE + b"\x02" + KEY))], corrupt("journal 0 not-a-record"))
    # No sequence number left to give.
    case([(b"journal", fmt), (named("t", LIMIT - 1), b"")], corrupt("exhausted"))
    case([(b"journal", fmt), (named("t", LIMIT - 2), b"")],
         ok(KEY, LIMIT - 1, first, [], [], [f"remove:{named('t', LIMIT - 2).hex()}", "sync-dir"]))
    case([(b"journal", fmt + b"\x00"), (named("q", LIMIT - 2), b"")], corrupt("exhausted"))
    case([(b"journal", fmt + b"\x00"), (named("q", LIMIT - 3), b"")],
         ok(KEY, LIMIT - 1, first, [], [LIMIT - 3, LIMIT - 2], keep_and_cut(fmt + b"\x00", first, LIMIT - 2)))
    # A torn tail — a commit or a start cut short, or zeros — kept under the next number, cut, and
    # that number skipped.
    c1, c2 = commit(1, 1), commit(2, 2)
    j, files = store([c1])
    tails = [torn_after(KEY, j, c2, n) for n in (1, J.HEADER, len(J.encoded(KEY, len(j), c2)) - 1)]
    tails += [torn_after(KEY, j, start, n) for n in (1, J.START_FRAME - 1)]
    tails += [j + bytes(J.HEADER + 5)]
    for t in tails:
        case([(b"journal", t), *files[1:]], ok(KEY, 3, len(j), [c1], [2], keep_and_cut(t, len(j), 2)))
    t = torn_after(KEY, fmt, start, 5)
    case([(b"journal", t)], ok(KEY, 2, first, [], [1], keep_and_cut(t, first, 1)))
    # The file of the torn commit in place, set aside; a temporary file removed.
    t = torn_after(KEY, j, c2, 7)
    case([(b"journal", t), files[1], (named("a", 2), b"\x00"), (named("t", 3), b"\x00")],
         ok(KEY, 5, len(j), [c1], [2, 4],
            [*keep_and_cut(t, len(j), 4), f"rename:{named('a', 2).hex()}:{named('q', 2).hex()}",
             f"remove:{named('t', 3).hex()}", "sync-dir"]))
    # Two crossposts answered, then a third whose record is whole but was not answered: all three
    # recover. Torn instead, its file is set aside.
    x1, x2 = commit(1, 1, more=((more, 1),)), commit(2, 2, more=((more, 2),))
    x3 = commit(3, 3, more=((more, 3),))
    j3, files3 = store([x1, x2, x3])
    case(files3, ok(KEY, 4, len(j3), [x1, x2, x3], [], []))
    j2, files2 = store([x1, x2])
    t = torn_after(KEY, j2, x3, J.HEADER + 3)
    case([(b"journal", t), *files2[1:], (named("a", 3), b"\x00")],
         ok(KEY, 5, len(j2), [x1, x2], [3, 4],
            [*keep_and_cut(t, len(j2), 4), f"rename:{named('a', 3).hex()}:{named('q', 3).hex()}", "sync-dir"]))
    # Final files no record names, the journal read cleanly: removed, unless a tail kept before is
    # numbered above it or it is set aside already.
    j, files = store([c1])
    case([*files, (named("a", 2), b"")],
         ok(KEY, 3, len(j), [c1], [], [f"remove:{named('a', 2).hex()}", "sync-dir"]))
    case([*files, (named("a", 2), b""), (named("j", 3), b"")],
         ok(KEY, 4, len(j), [c1], [2, 3], [f"rename:{named('a', 2).hex()}:{named('q', 2).hex()}", "sync-dir"]))
    case([*files, (named("a", 2), b""), (named("j", 2), b"")],
         ok(KEY, 3, len(j), [c1], [2], [f"remove:{named('a', 2).hex()}", "sync-dir"]))
    case([*files, (named("j", 3), b""), (named("a", 4), b"")],
         ok(KEY, 5, len(j), [c1], [3], [f"remove:{named('a', 4).hex()}", "sync-dir"]))
    case([*files, (named("a", 2), b""), (named("q", 2), b""), (named("j", 3), b"")],
         ok(KEY, 4, len(j), [c1], [2, 3], [f"remove:{named('a', 2).hex()}", "sync-dir"]))
    case([*files, (named("q", 7), b"x"), (named("j", 5), b"y")], ok(KEY, 8, len(j), [c1], [7, 5], []))
    case([*files, (named("t", 1), b"")],
         ok(KEY, 2, len(j), [c1], [], [f"remove:{named('t', 1).hex()}", "sync-dir"]))
    return out


def random_commits(rng: random.Random, groups: list[bytes]) -> list[J.Commit]:
    """Commits whose article numbers rise in each group, perhaps one breaking a rule across
    records: a sequence number another has, an article number not above, a group not carried."""
    highest: dict[bytes, int] = {}
    cs = []
    for seq in sorted(rng.sample(range(1, 40), rng.randint(0, 6))):
        named_groups = []
        for g in rng.sample(groups, rng.randint(1, len(groups))):
            highest[g] = highest.get(g, 0) + rng.choice([1, 1, 2, 1000])
            named_groups.append((g, min(highest[g], J.ARTICLES)))
        size = rng.choice([0, 1, 3, 70])
        cs.append((seq, rng.randbytes(rng.randint(1, 20)), tuple(named_groups), rng.randint(0, size), size,
                   rng.getrandbits(32)))
    if cs and rng.random() < 0.25:
        k = rng.randrange(len(cs))
        seq, message_id, (first, *rest), header, size, crc = cs[k]
        match rng.randrange(3):
            case 0:
                seq = rng.choice(cs)[0]
            case 1:
                first = (first[0], rng.randint(1, first[1]))
            case _:
                rest = [g for g in rest if g[0] != b"local.zzz"] + [(b"local.zzz", 1)]
        cs[k] = (seq, message_id, (first, *rest), header, size, crc)
    return cs


def with_starts(rng: random.Random, cs: list[J.Commit]) -> list[J.Item]:
    """The commits in their order, a start before some and perhaps one after the last."""
    items: list[J.Item] = []
    for c in cs:
        if rng.random() < 0.3:
            items.append(J.START_RECORD)
        items.append(c)
    if rng.random() < 0.3:
        items.append(J.START_RECORD)
    return items


def random_store(rng: random.Random) -> tuple[bytes, list[bytes], Files]:
    """A key, the groups the store carries and a directory recovery may find: a journal of commits
    and starts, perhaps ending in a commit or a start cut short or in zeros, a file for each number,
    files set aside, temporary and final files."""
    key = rng.choice([KEY, OTHER_KEY, rng.randbytes(16)])
    groups = rng.sample([b"local.test", b"local.more", b"a", b"b" * 64, b"comp.x"], rng.randint(1, 5))
    cs = random_commits(rng, groups)
    j = J.journal(key, with_starts(rng, cs))
    match rng.randrange(5):
        case 0 | 1:
            tail = J.encoded(key, len(j), rng.choice([commit(rng.randint(1, 50)), J.START_RECORD]))
            j += tail[:rng.randint(1, len(tail) - 1)]
        case 2:
            j += bytes(rng.randint(1, 40))
        case _:
            pass
    sized = sizes(cs)
    files = [(b"journal", j), *((named("a", s), rng.randbytes(n)) for s, n in sized.items())]
    for _ in range(rng.randint(0, 4)):
        letter = rng.choice("atqj")
        seq = rng.randint(1, 60)
        name = named(letter, seq)
        if (letter == "a" and seq in sized) or any(n == name for n, _ in files):
            continue
        files.append((name, rng.randbytes(rng.randint(0, 3))))
    rng.shuffle(files)
    return key, groups, files


def damaged(rng: random.Random, files: Files) -> Files:
    """The directory with one thing changed: a byte of a file, a file dropped, grown or emptied, or
    a name of no shape added."""
    out = list(files)
    k = rng.randrange(len(out))
    name, data = out[k]
    match rng.randrange(5):
        case 0 if data:
            at = rng.randrange(len(data))
            out[k] = (name, data[:at] + bytes([data[at] ^ (1 << rng.randrange(8))]) + data[at + 1:])
        case 1:
            del out[k]
        case 2:
            out[k] = (name, data + b"\x00")
        case 3 if data:
            out[k] = (name, b"")
        case _:
            out.insert(rng.randrange(len(out) + 1), (rng.choice([b"x", b"journal.old", named("a", 1)[:-1]]), b""))
    return out


def drawn(rng: random.Random) -> list[Case]:
    out = []
    for _ in range(600):
        key, groups, files = random_store(rng)
        out.append(Case(recover_line(files, key=key, groups=groups)))
        out.append(Case(recover_line(damaged(rng, files), key=key, groups=groups)))
    return out


def actions_drawn(rng: random.Random) -> list[Case]:
    """Actions done on small directories: names that exist and names that do not, a rename onto a
    name taken, a cut past the end, a journal created over one."""
    pool = [b"journal", named("a", 1), named("q", 1), named("j", 2), named("t", 3), b"x"]
    out = []
    for _ in range(300):
        files = [(n, rng.randbytes(rng.randint(0, 4))) for n in rng.sample(pool, rng.randint(0, len(pool)))]
        acts = []
        for _ in range(rng.randint(0, 5)):
            match rng.randrange(6):
                case 0:
                    acts.append(f"keep:{rng.choice(pool).hex()}:{hexed(rng.randbytes(rng.randint(0, 3)))}")
                case 1:
                    acts.append(f"rename:{rng.choice(pool).hex()}:{rng.choice(pool).hex()}")
                case 2:
                    acts.append(f"remove:{rng.choice(pool).hex()}")
                case 3:
                    acts.append("sync-dir")
                case 4:
                    acts.append(f"cut:{rng.randint(0, 6)}")
                case _:
                    acts.append(f"create:{rng.choice([KEY, OTHER_KEY]).hex()}")
        out.append(Case(f"apply {image(files)} {';'.join(acts) or '-'}"))
    return out


def field(answer: str, n: int) -> str:
    return answer.split(" ")[n]


def differing(asked: list[str], model: list[str], reference: list[str]) -> str | None:
    """The first case the model and the reference answer otherwise, and both answers."""
    for line, a, b in zip(asked, model, reference, strict=True):
        if a != b:
            return f"{line[:300]}: the model answers {a[:300]}, the reference {b[:300]}"
    return None


def unseen(answers: list[str]) -> list[str]:
    """The ways of finding a store corrupt that no answer shows."""
    seen = {field(a, 1) for a in answers if a.startswith("corrupt ")}
    return [f for f in FAULTS if f not in seen]


def again_problem(first: str, second: str) -> str | None:
    """What is wrong with `second`, how recovery answers on what the actions of `first` left: it has
    to start with the same key, end of the journal, articles and files set aside, a next number no
    higher, and nothing to do."""
    if not second.startswith("ok "):
        return "it does not recover"
    for k, what in ((1, "key"), (3, "end of the journal"), (4, "articles")):
        if field(second, k) != field(first, k):
            return f"its {what} changed"
    if int(field(second, 2)) > int(field(first, 2)):
        return "its next number is higher"
    if sorted(field(second, 5).split(",")) != sorted(field(first, 5).split(",")):
        return "other files are set aside"
    if field(second, 6) != "-":
        return "actions are left"
    return None


def section(text: str, start: str, end: str) -> str:
    """The part of `text` from `start` to the first `end` after it."""
    at = text.index(start)
    return text[at:text.index(end, at + len(start))]


def misstated(text: str, measured: dict[str, str]) -> list[str]:
    """Each phrase of `measured` that `text` states after no number, or anywhere after another
    number than the one measured."""
    wrong = []
    for phrase, value in measured.items():
        stated = re.findall(rf"(\d[\d,]*) {re.escape(phrase)}", text)
        if not stated or any(s != value for s in stated):
            wrong.append(f"{phrase!r}: {', '.join(stated) or 'none'}, not {value}")
    return wrong


def check() -> Report:
    OUT.mkdir(parents=True, exist_ok=True)
    python = str(lanes.pinned_python(REQUIREMENTS))
    rng = random.Random(SEED)  # noqa: S311 -- a fixed seed, so that every run draws the same cases
    steps, mark = {}, time.monotonic()
    families = {"table": table(), "drawn": drawn(rng), "actions": actions_drawn(rng)}
    cases = [c for family in families.values() for c in family]
    lines = [c.line for c in cases]
    steps["cases"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    model_command = [str(lanes.DN_COMPILER), "recovery-model"]
    reference_command = [python, str(REFERENCE)]

    def both(asked: list[str]) -> list[str]:
        model = C.answer_lines(model_command, asked, C.WORKERS)
        problem = differing(asked, model, C.answer_lines(reference_command, asked, C.WORKERS))
        if problem:
            raise LaneError(problem)
        return model

    answers = both(lines)
    steps["recover"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    for case, said in zip(cases, answers, strict=True):
        if not case.holds(said):
            raise LaneError(f"{case.line[:300]}: answered {said[:300]}, not {case.want}")
    if unseen(answers):
        raise LaneError(f"no directory found corrupt for {unseen(answers)}")
    recovered = [(ln, a) for ln, a in zip(lines, answers, strict=True) if a.startswith("ok ")]
    applied = both([f"apply {ln.split(' ')[3]} {field(a, 6)}" for ln, a in recovered])
    again = [(f"recover {' '.join(ln.split(' ')[1:3])} {after}", a)
             for (ln, a), after in zip(recovered, applied, strict=True)]
    answered_again = both([ln for ln, _ in again])
    for (line, first), second in zip(again, answered_again, strict=True):
        problem = again_problem(first, second)
        if problem:
            raise LaneError(f"{line[:300]}: after the actions of {first[:200]}, {problem}: {second[:200]}")
    steps["again"], mark = round(time.monotonic() - mark, 1), time.monotonic()
    for asked in REFUSED:
        for command in (model_command, reference_command):
            done = subprocess.run(command, input=asked + "\n", capture_output=True, text=True, timeout=600,
                                  check=False)
            if done.returncode == 0:
                raise LaneError(f"{command[-1]} answered a line no case may be: {asked!r}")
    held = list(zip(lines, answers, strict=True)) + list(zip([ln for ln, _ in again], answered_again, strict=True))
    where = {ln: f"again {k}" for k, (ln, _) in enumerate(again)}
    where |= {c.line: f"{name} {k}" for name, family in families.items() for k, c in enumerate(family)}
    caught = {}
    for mutant in MUTANTS:
        differs = C.first_difference([*model_command, "--mutant", mutant], held)
        if differs is None:
            raise LaneError(f"the version {mutant} was not caught")
        caught[mutant] = where[differs]
    steps["mutants"] = round(time.monotonic() - mark, 1)
    measured = {"cases": f"{len(cases):,}", "versions of recovery": f"{len(MUTANTS):,}",
                "directories of the table": f"{len(families['table']):,}",
                "directories drawn": f"{len(families['drawn']) // 2:,}",
                "lists of actions": f"{len(families['actions']):,}", "that recover": f"{len(recovered):,}"}
    baseline = (lanes.ROOT / "docs/baseline.md").read_text()
    assurance = (lanes.ROOT / "docs/assurance.md").read_text()
    wrong = misstated(section(baseline, "\n| Store |", "\n|") + section(baseline, "\n### Store\n", "\n### "),
                      measured)
    wrong += misstated(section(assurance, "\n| Recovery (`DN.News.Recovery`", "\n|"),
                       {k: measured[k] for k in ("cases", "versions of recovery", "that recover")})
    if wrong:
        raise LaneError(f"the documents state otherwise than measured: {wrong}")
    seen = [field(a, 1) for a in answers if a.startswith("corrupt ")]
    return Report("checked", None, [REFERENCE, REQUIREMENTS], {
        "cases": len(cases), "by_family": {k: len(v) for k, v in families.items()},
        "recovered": len(recovered), "recovered_again": len(again),
        "faults_seen": {f: seen.count(f) for f in FAULTS}, "refused_lines": len(REFUSED),
        "mutants_caught": caught, "seconds_by_step": steps})


def main() -> None:
    lanes.lane_main("STORE", OUT, check)


if __name__ == "__main__":
    main()
