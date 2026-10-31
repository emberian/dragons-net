#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
"""The Lean model of Pancake against HOL4's own semantics, on the state corpus.

`backend/semantics/states.txt` is what `dn-compiler dump-states` prints: each case of
`DN.Compiler.StateCorpus` with the state the Lean model ends in (the state lane holds the file
equal to the printer). `write` turns the input half of every case into a HOL term, `panSem`'s
`evaluate` on the program and the state, under `dn_show` of `backend/semantics/dnShowScript.sml`,
which prints the answer in the dump's own form; the theory it writes evaluates each with `EVAL`.
`compare` reads what the theory printed and requires every field of every case to be the
model's. Only the input fields are read: the answers come from HOL, so a converter that copied
the model's answer would have nothing to copy from.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
# The path above is what makes this importable.
from state_corpus import FIELDS, pairs, parse_cases, parse_sexp

BINOPS = {"add": "asm$Add", "and": "asm$And", "sub": "asm$Sub", "xor": "asm$Xor", "or": "asm$Or"}
CMPS = {"less": "asm$Less", "equal": "asm$Equal", "notless": "asm$NotLess"}
# The planted defect: subtraction read as addition. A comparison that misses it compares nothing.
DEFECT = {**BINOPS, "sub": "asm$Add"}
INPUTS = ("CASE", "PROG", "CODE", "LOCALS", "MEM", "DOM", "BE", "CLOCK", "BASE", "ANSWERS", "NAMES")
WRITE_INPUTS = ("WRITE", "WDOM", "WBE", "WADDR", "WBYTES", "WMEM")


def word(n: str) -> str:
    return f"({int(n)}w : word64)"


def plain(x: str, allowed: str = r"[A-Za-z0-9_]*") -> str:
    """Text that goes into an SML or HOL string literal as it is."""
    if not re.fullmatch(allowed, x):
        raise SystemExit(f"semantics check: {x!r} cannot be written into the theory as it is")
    return x


def name(x: str) -> str:
    return f'(strlit "{plain(x)}")'


def exp(e: Any, ops: dict[str, str]) -> str:
    head = e[0]
    if head == "const":
        return f"(panLang$Const {word(e[1])})"
    if head == "var":
        return f"(panLang$Var panLang$Local {name(e[1])})"
    if head == "base":
        return "panLang$BaseAddr"
    if head in ops:
        return f"(panLang$Op {ops[head]} [{exp(e[1], ops)}; {exp(e[2], ops)}])"
    if head == "mul":
        return f"(panLang$Panop panLang$Mul [{exp(e[1], ops)}; {exp(e[2], ops)}])"
    if head in CMPS:
        return f"(panLang$Cmp {CMPS[head]} {exp(e[1], ops)} {exp(e[2], ops)})"
    if head == "loadb":
        return f"(panLang$LoadByte {exp(e[1], ops)})"
    if head == "loadw":
        return f"(panLang$Load panLang$One {exp(e[1], ops)})"
    if head in ("shr", "shl"):
        # The source language shifts by an expression; panLang's `Shift` takes a number, and the
        # model's clause for a literal distance is the one the corpus reaches.
        if e[2][0] != "const":
            raise SystemExit(f"semantics check: a shift by other than a literal: {e}")
        return f"(panLang$Shift {'ast$Lsr' if head == 'shr' else 'ast$Lsl'} {exp(e[1], ops)} {int(e[2][1])})"
    raise SystemExit(f"semantics check: no HOL form for the expression {e}")


def prog(p: Any, ops: dict[str, str]) -> str:
    head = p[0]
    if head == "skip":
        return "panLang$Skip"
    if head == "dec":
        return f"(panLang$Dec {name(p[1])} panLang$One {exp(p[2], ops)} {prog(p[3], ops)})"
    if head == "assign":
        return f"(panLang$Assign panLang$Local {name(p[1])} {exp(p[2], ops)})"
    if head == "store":
        return f"(panLang$Store {exp(p[1], ops)} {exp(p[2], ops)})"
    if head == "storeb":
        return f"(panLang$StoreByte {exp(p[1], ops)} {exp(p[2], ops)})"
    if head == "extcall":
        args = " ".join(exp(a, ops) for a in p[2:6])
        return f"(panLang$ExtCall {name('' if p[1] == '_' else p[1])} {args})"
    if head == "seq":
        return f"(panLang$Seq {prog(p[1], ops)} {prog(p[2], ops)})"
    if head == "if":
        return f"(panLang$If {exp(p[1], ops)} {prog(p[2], ops)} {prog(p[3], ops)})"
    if head == "while":
        return f"(panLang$While {exp(p[1], ops)} {prog(p[2], ops)})"
    if head == "ret":
        return f"(panLang$Return {exp(p[1], ops)})"
    if head == "deccall":
        args = "; ".join(exp(a, ops) for a in p[3])
        return f"(panLang$DecCall {name(p[1])} panLang$One {name(p[2])} [{args}] {prog(p[4], ops)})"
    raise SystemExit(f"semantics check: no HOL form for the statement {p}")


def bytes_of(text: str) -> str:
    if text in ("", "-"):
        return "([] : word8 list)"
    return "[" + "; ".join(f"({int(text[i:i + 2], 16)}w : word8)" for i in range(0, len(text), 2)) + "]"


def oracle(answers: list[str]) -> str:
    """`oracleOf`: answer `i` to call `i`, the ffi state the call count; past the list, the array
    handed back unchanged."""
    body = "Oracle_return (i + 1) arr"
    for k in reversed(range(len(answers))):
        a = answers[k]
        if a.startswith("ret:"):
            reply = f"Oracle_return (i + 1) {bytes_of(a[4:])}"
        elif a == "short":
            reply = "Oracle_return (i + 1) (DROP 1 arr)"
        elif a in ("final:failed", "final:diverged"):
            reply = f"Oracle_final FFI_{a[6:]}"
        else:
            raise SystemExit(f"semantics check: no HOL form for the answer {a}")
        body = f"(if i = {k} then {reply} else {body})"
    return f"(\\(nm : ffiname) (i : num) (conf : word8 list) (arr : word8 list). {body})"


def memory(text: str) -> str:
    body = "0w"
    for a, w in reversed(pairs(text)):
        body = f"(if a = {word(a)} then {word(w)} else {body})"
    return f"(\\a. {body})"


def domain(text: str) -> tuple[str, str]:
    """The domain as a set, for the state, and as a list, for printing."""
    dom = [word(a) for a in text.split(",") if a]
    if not dom:
        return "({} : word64 set)", "([] : word64 list)"
    return "{" + "; ".join(dom) + "}", "[" + "; ".join(dom) + "]"


def code(text: str, ops: dict[str, str]) -> str:
    functions, _ = parse_sexp(text)
    out = "(FEMPTY : mlstring |-> ((mlstring # shape) list # 64 panLang$prog))"
    for f, params, body in functions:
        shapes = "; ".join(f"({name(x)}, panLang$One)" for x in params)
        shapes = f"[{shapes}]" if params else "([] : (mlstring # shape) list)"
        out += f" |+ ({name(f)}, ({shapes}, {prog(body, ops)}))"
    return f"({out})"


def case_term(case: dict[str, str], ops: dict[str, str]) -> tuple[str, str]:
    """The key of a case and the HOL term whose value is its printed answer."""
    if "WRITE" in case:
        dom_set, dom_list = domain(case["WDOM"])
        be = "T" if case["WBE"] == "1" else "F"
        written = (f"dn_written {dom_list} (write_bytearray {word(case['WADDR'])} {bytes_of(case['WBYTES'])}"
                   f" (\\a. Word ({memory(case['WMEM'])} a)) {dom_set} {be})")
        return ("WRITE " + case["WRITE"], written)
    program, _ = parse_sexp(case["PROG"])
    dom_set, dom_list = domain(case["DOM"])
    locals_ = "".join(f" |+ ({name(k)}, ValWord {word(v)})" for k, v in pairs(case["LOCALS"]))
    answers = [a for a in case["ANSWERS"].split(";") if a]
    state = (f"<| locals := FEMPTY{locals_}; globals := FEMPTY; structs := []; code := {code(case['CODE'], ops)};"
             f" eshapes := FEMPTY; memory := (\\a. Word ({memory(case['MEM'])} a)); memaddrs := {dom_set};"
             f" sh_memaddrs := {{}}; clock := {int(case['CLOCK'])}; be := {'T' if case['BE'] == '1' else 'F'};"
             f" ffi := <| oracle := {oracle(answers)}; ffi_state := (0 : num); io_events := [] |>;"
             f" base_addr := {word(case['BASE'])}; top_addr := 0w |>")
    names = "[" + "; ".join(f'"{plain(n)}"' for n in case["NAMES"].split(",") if n) + "]"
    if names == "[]":
        names = "([] : string list)"
    shown = (f"dn_show {names} {dom_list} (panSem$evaluate ({prog(program, ops)} : 64 panLang$prog,"
             f" ({state} : (64, num) panSem$state)))")
    return ("CASE " + case["CASE"], shown)


# The same cases as terms of dnModel, the Lean model written in HOL, which dnModelProof proves
# equal to panSem's evaluate: this run shows the transliteration answers as the Lean model does.
MODEL_BINOPS = {"add": "BAdd", "and": "BAnd", "sub": "BSub", "xor": "BXor", "or": "BOr"}
MODEL_DEFECT = {**MODEL_BINOPS, "sub": "BAdd"}
MODEL_CMPS = {"less": "CLess", "equal": "CEqual", "notless": "CNotLess"}
MODEL_UNARY = {"loadb": "ELoadByte", "loadw": "ELoadWord"}
MODEL_BINARY = {"mul": "EMul", "shr": "EShiftR", "shl": "EShiftL"}


def hol_string(x: str) -> str:
    return f'"{plain(x)}"'


def model_exp(e: Any, ops: dict[str, str]) -> str:
    head = e[0]
    if head == "const":
        return f"(EConst {word(e[1])})"
    if head == "var":
        return f"(EVar {hol_string(e[1])})"
    if head == "base":
        return "EBase"
    if head in ops:
        return f"(EOp {ops[head]} {model_exp(e[1], ops)} {model_exp(e[2], ops)})"
    if head in MODEL_BINARY:
        return f"({MODEL_BINARY[head]} {model_exp(e[1], ops)} {model_exp(e[2], ops)})"
    if head in MODEL_CMPS:
        return f"(ECmp {MODEL_CMPS[head]} {model_exp(e[1], ops)} {model_exp(e[2], ops)})"
    if head in MODEL_UNARY:
        return f"({MODEL_UNARY[head]} {model_exp(e[1], ops)})"
    raise SystemExit(f"semantics check: no dnModel form for the expression {e}")


def model_prog(p: Any, ops: dict[str, str]) -> str:
    head = p[0]
    if head == "skip":
        return "PSkip"
    if head == "dec":
        return f"(PDec {hol_string(p[1])} {model_exp(p[2], ops)} {model_prog(p[3], ops)})"
    if head == "assign":
        return f"(PAssign {hol_string(p[1])} {model_exp(p[2], ops)})"
    if head in ("store", "storeb"):
        return f"({'PStore' if head == 'store' else 'PStoreByte'} {model_exp(p[1], ops)} {model_exp(p[2], ops)})"
    if head == "extcall":
        args = " ".join(model_exp(a, ops) for a in p[2:6])
        return f"(PExtCall {hol_string('' if p[1] == '_' else p[1])} {args})"
    if head == "seq":
        return f"(PSeq {model_prog(p[1], ops)} {model_prog(p[2], ops)})"
    if head == "if":
        return f"(PCond {model_exp(p[1], ops)} {model_prog(p[2], ops)} {model_prog(p[3], ops)})"
    if head == "while":
        return f"(PWhile {model_exp(p[1], ops)} {model_prog(p[2], ops)})"
    if head == "ret":
        return f"(PRet {model_exp(p[1], ops)})"
    if head == "deccall":
        args = "; ".join(model_exp(a, ops) for a in p[3])
        args = f"[{args}]" if p[3] else "([] : dn_exp list)"
        return f"(PDecCall {hol_string(p[1])} {hol_string(p[2])} {args} {model_prog(p[4], ops)})"
    raise SystemExit(f"semantics check: no dnModel form for the statement {p}")


def model_oracle(answers: list[str]) -> str:
    """`oracleOf`: the world is the call count and the record of every call it answered."""
    record = 'name ++ ":" ++ dn_hexs conf ++ ":" ++ dn_hexs arr'
    body = "ORet (i + 1, trace ++ [rec]) arr"
    for k in reversed(range(len(answers))):
        a = answers[k]
        if a.startswith("ret:"):
            reply = f"ORet (i + 1, trace ++ [rec]) {bytes_of(a[4:])}"
        elif a == "short":
            reply = "ORet (i + 1, trace ++ [rec]) (DROP 1 arr)"
        elif a in ("final:failed", "final:diverged"):
            reply = f"OFinal {'OFailed' if a == 'final:failed' else 'ODiverged'}"
        else:
            raise SystemExit(f"semantics check: no dnModel form for the answer {a}")
        body = f"(if i = {k} then {reply} else {body})"
    return (f"(\\((i : num), (trace : string list)) (name : string) (conf : word8 list) (arr : word8 list)."
            f" let rec = {record} in {body})")


def predicate(text: str) -> str:
    """The domain as dnModel reads it: a predicate on addresses, as Lean's `memaddrs`."""
    dom = [word(a) for a in text.split(",") if a]
    return "(\\a. " + (" \\/ ".join(f"a = {a}" for a in dom) if dom else "F") + ")"


def model_case_term(case: dict[str, str], ops: dict[str, str]) -> tuple[str, str]:
    """The key of a case and the dnModel term whose value is its printed answer."""
    if "WRITE" in case:
        dom_set, dom_list = predicate(case["WDOM"]), domain(case["WDOM"])[1]
        be = "T" if case["WBE"] == "1" else "F"
        written = (f"dn_model_written {dom_list} (dn_write_byte_array {dom_set} {be} {word(case['WADDR'])}"
                   f" {bytes_of(case['WBYTES'])} {memory(case['WMEM'])})")
        return ("WRITE " + case["WRITE"], written)
    program, _ = parse_sexp(case["PROG"])
    functions, _ = parse_sexp(case["CODE"])
    dom_set, dom_list = predicate(case["DOM"]), domain(case["DOM"])[1]
    locals_ = "NONE"
    for k, v in reversed(pairs(case["LOCALS"])):
        locals_ = f"(if k = {hol_string(k)} then SOME {word(v)} else {locals_})"
    code = "NONE"
    for f, params, body in reversed(functions):
        names = "[" + "; ".join(hol_string(x) for x in params) + "]" if params else "([] : string list)"
        code = f"(if f = {hol_string(f)} then SOME ({names}, {model_prog(body, ops)}) else {code})"
    answers = [a for a in case["ANSWERS"].split(";") if a]
    state = (f"<| locals := (\\k. {locals_}); memory := {memory(case['MEM'])}; memaddrs := {dom_set};"
             f" be := {'T' if case['BE'] == '1' else 'F'}; clock := {int(case['CLOCK'])};"
             f" ffi := ((0 : num), ([] : string list)); baseAddr := {word(case['BASE'])};"
             f" code := (\\f. {code}) |>")
    names = "[" + "; ".join(hol_string(n) for n in case["NAMES"].split(",") if n) + "]"
    if names == "[]":
        names = "([] : string list)"
    shown = (f"dn_model_show {names} {dom_list} (dn_sem {model_oracle(answers)} {model_prog(program, ops)}"
             f" ({state} : (num # string list) dn_state))")
    return ("CASE " + case["CASE"], shown)


PREAMBLE = """(* Written by scripts/semantics_check.py from backend/semantics/states.txt. *)
open HolKernel boolLib bossLib wordsLib panLangTheory panSemTheory ffiTheory dnShowTheory THEORIES;

val _ = new_theory "NAME";

(* A term that does not reduce to a string prints as such, and is compared and refused. *)
fun answer (key, tm) =
  let
    val text = stringSyntax.fromHOLstring (rhs (concl (EVAL tm))) handle HOL_ERR _ => "UNREDUCED"
  in
    print ("MARK " ^ key ^ "\\n" ^ text ^ "\\nDNEND\\n")
  end;
"""
# Each theory prints under its own word, so that one build log carries both.
PANSEM, MODEL = "DNCASE", "DNMODEL"


def script(cases: list[dict[str, str]], ops: dict[str, str], model: bool = False) -> str:
    """The theory that evaluates every case: by panSem, or by dnModel."""
    name, mark, extra = ("dnModelStates", MODEL, "dnModelTheory dnModelShowTheory") if model else (
        "dnStates", PANSEM, "")
    lines = [PREAMBLE.replace("NAME", name).replace("MARK", mark).replace(" THEORIES", (" " + extra) if extra else "")]
    for case in cases:
        key, term = (model_case_term if model else case_term)(case, ops)
        lines.append(f'val _ = answer ("{plain(key, r"[A-Za-z0-9_ -]+")}", ``{term}``);\n')
    lines.append("val _ = export_theory ();\n")
    return "".join(lines)


def answered(log: str, mark: str = PANSEM) -> dict[str, list[str]]:
    """What a theory printed under its word, by case; a case printed twice is refused."""
    out: dict[str, list[str]] = {}
    for match in re.finditer(rf"^{mark} (.*)\n((?:(?!DNEND).*\n)*?)DNEND$", log, re.MULTILINE):
        key = match.group(1)
        if key in out:
            raise SystemExit(f"semantics check: {key} was printed twice")
        out[key] = match.group(2).splitlines()
    return out


def differences(cases: list[dict[str, str]], log: str, mark: str = PANSEM) -> list[tuple[str, str]]:
    """Every case whose fields HOL printed differently, or did not print, with what is wrong."""
    hol = answered(log, mark)
    found = []
    keys = set()
    for case in cases:
        writing = "WRITE" in case
        key = ("WRITE " + case["WRITE"]) if writing else ("CASE " + case["CASE"])
        keys.add(key)
        fields = ("WRESULT",) if writing else FIELDS
        ours = [f"{f} {case[f]}".rstrip() for f in fields]
        theirs = [line.rstrip() for line in hol.get(key, [])]
        if key not in hol:
            found.append((key, "HOL printed no answer"))
        elif ours != theirs:
            changed = [f"{a!r} against HOL's {b!r}" for a, b in zip(ours, theirs, strict=False) if a != b]
            found.append((key, f"the model's {'; '.join(changed) or ours} (HOL printed {len(theirs)} lines)"))
    found += [(key, "HOL answered a case the corpus does not have") for key in sorted(set(hol) - keys)]
    return found


def defect_unseen(cases: list[dict[str, str]], log: str, mark: str = PANSEM) -> str | None:
    """Why the planted defect's run does not show the comparison working, or None if it does: HOL
    answered every case, some differ, and each that differs has a subtraction to differ by."""
    found = differences(cases, log, mark)
    if not found:
        return f"the planted defect changed no answer of {mark}"
    subtracting = {"CASE " + c["CASE"] for c in cases if "CASE" in c and "(sub " in c["PROG"] + c["CODE"]}
    for key, problem in found:
        # A theory that answered nothing for a case would differ there and show nothing.
        if problem == "HOL printed no answer" or "UNREDUCED" in problem:
            return f"{key}: {problem}"
        if key not in subtracting:
            return f"{key} differs, which has no subtraction: {problem}"
    return None


def corpus(path: Path) -> list[dict[str, str]]:
    cases = parse_cases(path.read_text())
    for case in cases:
        fields = (*WRITE_INPUTS, "WRESULT") if "WRITE" in case else (*INPUTS, *FIELDS)
        missing = [f for f in fields if f not in case]
        if missing:
            raise SystemExit(f"semantics check: a case of {path} has no {', '.join(missing)}")
    return cases


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    write = sub.add_parser("write", help="write the HOL theories that evaluate every case")
    write.add_argument("corpus", type=Path)
    write.add_argument("dir", type=Path, help="where dnStatesScript.sml and dnModelStatesScript.sml go")
    write.add_argument("--defect", action="store_true", help="read subtraction as addition")
    compare = sub.add_parser("compare", help="compare what the theories printed with the model")
    compare.add_argument("corpus", type=Path)
    compare.add_argument("log", type=Path)
    compare.add_argument("--expect-differences", action="store_true",
                         help="succeed only if the planted defect is seen: its run")
    args = parser.parse_args()
    cases = corpus(args.corpus)
    if args.command == "write":
        (args.dir / "dnStatesScript.sml").write_text(script(cases, DEFECT if args.defect else BINOPS))
        (args.dir / "dnModelStatesScript.sml").write_text(
            script(cases, MODEL_DEFECT if args.defect else MODEL_BINOPS, model=True))
        return 0
    log = args.log.read_text(errors="replace")
    states = sum(1 for c in cases if "CASE" in c)
    if args.expect_differences:
        for mark in (PANSEM, MODEL):
            unseen = defect_unseen(cases, log, mark)
            if unseen is not None:
                print(f"DN SEMANTICS: {unseen}; the comparison is not shown to compare", file=sys.stderr)
                return 1
        print("DN SEMANTICS: the planted defect is seen by panSem and by dnModel, each time where a case"
              " subtracts")
        return 0
    failed = False
    for mark, what in ((PANSEM, "panSem's evaluate"), (MODEL, "dnModel's dn_sem")):
        found = differences(cases, log, mark)
        for key, problem in found:
            print(f"DN SEMANTICS: {what}: {key}: {problem}", file=sys.stderr)
        if found:
            print(f"DN SEMANTICS: {len(found)} of {len(cases)} cases disagree with {what}", file=sys.stderr)
            failed = True
        else:
            print(f"DN SEMANTICS: {states} cases and {len(cases) - states} write-backs agree with {what}"
                  " on every field")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
