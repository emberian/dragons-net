-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfRules
import DN.Compiler.Checked
import DN.Compiler.Analyzer

/-!
# DN.News.AbnfProg

The grammar of `DN.News.AbnfRules` as Pancake functions, which say of a rule what
`DN.News.Abnf.matches?` says: whether it matches all of an input. A function takes a set of
positions to the set of positions a match of its rule from one of them can end at, as `endsFrom`
does, a set at a time. A set is bits over the positions of the input with the window of words that
holds them, in a slot of the area; a function's own sets lie in a frame of slots of its own.

A term that matches one byte of a class, or one string, is a leaf: `leafClass` and `leafText` read
it from a table. The grammar's one cycle, a comment within a comment (RFC 5322 §3.2.2), is read by
`ruleComment`, a scan with a count of depth: a comment's end is the first `)` its depth closes. So
no function calls itself or one that calls it, the functions come in an order in which each calls
only those before it, and each frame lies past the frames of every function that calls it, so no
two functions running at once share a slot. Tested against `dn-compiler abnf-model`, not proven.

So that the analysis of decision 0004 sees every access lie in the area, a set holds no address,
and a function checks each slot it is given and each word it reads back before it makes an address
of it: one out of range sets the area's flag of a failed check and returns 1, and the program
answers 2.
-/

namespace DN.News.AbnfProg

open DN.Compiler DN.Compiler.Syntax DN.News.Abnf DN.News.AbnfRules

/-! ## The grammar's leaves, functions and frames -/

/-- Defects a version of the program may carry, each of which the grammar lane has to see. -/
inductive Mutant
  | none
  /-- a repetition goes on past its upper bound -/
  | repPastBound
  /-- a choice leaves out its last alternative -/
  | altLast
  /-- a quoted string matches letters only in the case written -/
  | caseful
  /-- a comment takes `\` for text -/
  | commentEscape
  /-- a comment's white space may fold twice -/
  | commentFold
  /-- a union keeps the window it had below the words it adds -/
  | unionWindow
  /-- a set built from positions out of order takes its window from the first and the last -/
  | windowOrder
  /-- no function checks the slots it is given, which only the analysis can see -/
  | unchecked
  deriving DecidableEq, Inhabited

def mutantNames : List (String × Mutant) :=
  [("rep-past-bound", .repPastBound), ("alt-last", .altLast), ("caseful", .caseful),
   ("comment-escape", .commentEscape), ("comment-fold", .commentFold),
   ("union-window", .unionWindow), ("window-order", .windowOrder)]

def ruleIndex (s : String) : Nat := (names.findIdx? (· == s)).getD 0

def commentRule : Nat := ruleIndex "comment"

/-- Steps enough to follow a chain of rules through the grammar, and of terms within one. -/
def steps : Nat := 4 * grammar.size

/-- A letter in either case, or the byte itself. -/
def caseRanges (c : Nat) : List (Nat × Nat) :=
  if 65 ≤ c ∧ c ≤ 90 then [(c, c), (c + 32, c + 32)]
  else if 97 ≤ c ∧ c ≤ 122 then [(c - 32, c - 32), (c, c)]
  else [(c, c)]

/-- The bytes a term matches as ranges, when it matches exactly one byte: a range, a string of one
character, or a choice of such terms, directly or through rules. -/
def classOf : Nat → Term → Option (List (Nat × Nat))
  | 0, _ => none
  | _ + 1, .range lo hi => some [(lo, hi)]
  | _ + 1, .text s => match codes s with
    | [c] => some (caseRanges c)
    | _ => none
  | _ + 1, .exact [b] => some [(b, b)]
  | f + 1, .alt ts => (ts.mapM (classOf f)).map List.flatten
  | f + 1, .ref i => if i == commentRule then none else grammar[i]?.bind (classOf f)
  | _ + 1, _ => none

/-- The bytes a term matches when it matches one string, and whether letters match in either
case: a string, or a rule that is one. -/
def textOf : Nat → Term → Option (List Nat × Bool)
  | 0, _ => none
  | _ + 1, .text s => some ((codes s).map lower, true)
  | _ + 1, .exact s => some (s, false)
  | f + 1, .ref i => grammar[i]?.bind (textOf f)
  | _ + 1, _ => none

/-- What a leaf matches: a byte of a class, its 256 bits as four words; or a string. -/
inductive Leaf
  | cls (bits : List Nat)
  | text (bytes : List Nat) (caseless : Bool)
  deriving BEq, Inhabited

def bitsOf (rs : List (Nat × Nat)) : List Nat :=
  let set := (List.range 256).foldl
    (fun acc b => if rs.any (fun (lo, hi) => lo ≤ b && b ≤ hi) then acc + 2 ^ b else acc) 0
  (List.range 4).map fun k => set / 2 ^ (64 * k) % 2 ^ 64

def leafOf (t : Term) : Option Leaf :=
  match classOf steps t with
  | some rs => some (.cls (bitsOf rs))
  | none => (textOf steps t).map fun (bs, c) => .text bs (c && bs.any fun b => 97 ≤ b && b ≤ 122)

def termOf (i : Nat) : Term := grammar[i]?.getD (.alt [])

/-- Whether rule `i` has a function: the comment's, or one that is no leaf. -/
def hasFun (i : Nat) : Bool := i == commentRule || (leafOf (termOf i)).isNone

/-- The rules with functions a term calls, in order. -/
def callsOf : Nat → Term → List Nat
  | 0, _ => []
  | f + 1, t =>
    if (leafOf t).isSome then [] else
    match t with
    | .ref i => [i]
    | .seq ts | .alt ts => ts.flatMap (callsOf f)
    | .rep _ _ u => callsOf f u
    | _ => []

def callees (i : Nat) : List Nat :=
  if i == commentRule then [] else (callsOf steps (termOf i)).eraseDups

/-- The leaves a term reads, in order. -/
def leavesOf : Nat → Term → List Leaf
  | 0, _ => []
  | f + 1, t =>
    match leafOf t with
    | some l => [l]
    | none => match t with
      | .seq ts | .alt ts => ts.flatMap (leavesOf f)
      | .rep _ _ u => leavesOf f u
      | _ => []

/-- Rules `i` reaches, each after every rule it calls, after `done`. -/
def visit : Nat → Nat → List Nat → List Nat
  | 0, _, done => done
  | f + 1, i, done =>
    if done.contains i then done
    else (callees i).foldl (fun acc j => visit f j acc) done ++ [i]

/-- The rules with functions, each after those it calls. -/
def order : List Nat :=
  ((List.range grammar.size).filter hasFun).foldl (fun acc i => visit steps i acc) []

/-- Whether each function calls only functions before it: a cycle other than the comment's would
leave some function after one it calls. -/
def ordered : Bool :=
  (order.zipIdx).all fun (i, k) => (callees i).all fun j => (order.take k).contains j

/-- How many slots of its own a term's statements use. -/
def needOf : Nat → Term → Nat
  | 0, _ => 0
  | f + 1, t =>
    if (leafOf t).isSome then 0 else
    match t with
    | .seq [u] | .alt [u] => needOf f u
    | .seq (u :: us) => 2 + ((u :: us).map (needOf f)).foldl max 0
    | .alt (u :: us) => 1 + ((u :: us).map (needOf f)).foldl max 0
    | .rep 0 (some 1) u => needOf f u
    | .rep _ _ u => 2 + needOf f u
    | _ => 0

def need (i : Nat) : Nat := if i == commentRule then 0 else needOf steps (termOf i)

/-- The slots a run of the program keeps besides the frames: the input set and the answer. -/
def roots : Nat := 2

/-- Where each function's frame starts: past the frame of every function that calls it, worked
out from the callers down. -/
def frames : List (Nat × Nat) :=
  order.reverse.foldl (fun offs g =>
    let og := (offs.lookup g).getD roots
    (callees g).foldl (fun offs j =>
      let oj := (offs.lookup j).getD roots
      (j, max oj (og + need g)) :: offs.filter (·.1 != j)) offs)
    (order.map (·, roots))

def frameOf (i : Nat) : Nat := (frames.lookup i).getD roots

def slots : Nat := (order.map fun i => frameOf i + need i).foldl max roots

/-- The leaves every rule reads: those in a function's term, and a leaf rule's own. -/
def allLeaves : List Leaf :=
  (List.range grammar.size).flatMap fun i =>
    if hasFun i then (if i == commentRule then [] else leavesOf steps (termOf i))
    else (leafOf (termOf i)).toList

def classes : List (List Nat) :=
  (allLeaves.filterMap fun | .cls b => some b | _ => none).eraseDups

def texts : List (List Nat × Bool) :=
  (allLeaves.filterMap fun | .text b c => some (b, c) | _ => none).eraseDups

/-- The longest string a leaf may be (`regression_959`). -/
def textMax : Nat := 63

/-! ## The area -/

/-- The longest input: a header section's bound (decision 0005). -/
def inputMax : Nat := 65536

/-- Words of a set: positions up to `inputMax`, and one more word. -/
def setWords : Nat := inputMax / 64 + 2

/-- A set: the first and last words of its window, then its bits. Outside the window every bit is
clear and the words at its ends are not; an empty set's window is `[1, 0]`. -/
def sLo : Nat := 0
def sHi : Nat := 8
def sBits : Nat := 16
def setSize : Nat := sBits + 8 * setWords

/-! The area: the rule asked, the input's length and the answer; the flag of a failed check; the
positions the matches start from, as many as the word before them says; the powers of two below
2^64 and the masks of a word's bytes; each class, four words; each string's place among the
strings' bytes, its length and whether it is caseless; the strings' bytes; the input; the slots. -/

def aRule : Nat := 0
def aLen : Nat := 8
def aAnswer : Nat := 16
def aBroken : Nat := 24
def startsMax : Nat := 16
def aStarts : Nat := 32
def aStartList : Nat := aStarts + 8
def aPow : Nat := aStartList + 8 * startsMax
/-- The masks of a word's eight bytes. -/
def aMask : Nat := aPow + 8 * 64
def aClass : Nat := aMask + 8 * 8
def aTexts : Nat := aClass + 32 * classes.length
def textBytes : Nat := (texts.map (·.1.length)).sum
def aTextBytes : Nat := aTexts + 24 * texts.length
/-- Past the strings' bytes, room for a comparison from any place `leafText` accepts. -/
def aInput : Nat := aTextBytes + (textBytes + textMax + 1 + 7) / 8 * 8
/-- Every position a set can hold and a string past it: no read passes the input's length, but the
analysis, which does not relate a position to it, sees each read in the area. -/
def inputRoom : Nat := 64 * (setWords + 1)
def aSets : Nat := aInput + inputRoom
def size : Nat := aSets + slots * setSize

/-! ## Statements -/

def ne (a b : PExpr) : PExpr := eEq (eEq a b) (n 0)
/-- Either of two flags, each zero or one. -/
def or2 (a b : PExpr) : PExpr := eLt (n 0) (eAdd a b)
def inc (x : String) : PStmt := .assign x (eAdd (v x) (n 1))
def word (p : PExpr) (o : Nat) : PExpr := .loadw 1 (atOff p o)
def byte (p : PExpr) : PExpr := .loadb p
def all1 : Nat := 2 ^ 64 - 1

/-- Unless the local `x` lies in `[0, hi]`, the flag of a failed check set and 1 returned. -/
def kept (x : String) (hi : Nat) : PStmt :=
  .ite (or2 (eLt (v x) (n 0)) (eLt (n hi) (v x))) [.store (atOff (v "a") aBroken) (n 1), .ret (n 1)] []

/-- The area, at `ofs` from `@base`. -/
def areaAt (ofs : Nat) : PStmt := .dec "a" (atOff .base ofs)

/-- The slot numbered by the local `x`. -/
def slot (x : String) : PExpr := eAdd (atOff (v "a") aSets) (eMul (v x) (n setSize))

/-- Word `w` of the set at `p`. -/
def bitWord (p : String) (w : PExpr) : PExpr := eAdd (atOff (v p) sBits) (eMul w (n 8))

/-- The power of two `j`. -/
def pow (j : PExpr) : PExpr := .loadw 1 (eAdd (atOff (v "a") aPow) (eMul j (n 8)))

/-- The set at `q` given position `y` too, its window's ends so far in `dl` and `dh`, `df` set
while it is empty: the positions may come in any order. -/
def addBit (m : Mutant) (y : PExpr) : List PStmt :=
  [.dec "yw" (.shr y (n 6)), kept "yw" (setWords - 1), .dec "yj" (eAnd y (n 63)),
   .store (bitWord "q" (v "yw")) (eOr (.loadw 1 (bitWord "q" (v "yw"))) (pow (v "yj")))] ++
  if m == .windowOrder then
    [.ite (v "df") [.assign "dl" (v "yw"), .assign "df" (n 0)] [], .assign "dh" (v "yw")]
  else
    [.ite (v "df") [.assign "dl" (v "yw"), .assign "dh" (v "yw"), .assign "df" (n 0)]
      [.ite (eLt (v "yw") (v "dl")) [.assign "dl" (v "yw")] [],
       .ite (eLt (v "dh") (v "yw")) [.assign "dh" (v "yw")] []]]

/-- For each position `x` of the set at `p` below `nn`, `body`, from the lowest: a leaf matches at
least one byte (`regression_959`) and a comment starts with one. A word's bits are tried only in
its bytes that hold one. -/
def eachPos (body : List PStmt) : List PStmt :=
  [.dec "lo" (word (v "p") sLo), kept "lo" (setWords - 1),
   .dec "hi" (word (v "p") sHi), kept "hi" (setWords - 1),
   .dec "w" (v "lo"),
   .while (eLe (v "w") (v "hi"))
     [.dec "wd" (.loadw 1 (bitWord "p" (v "w"))),
      .ite (ne (v "wd") (n 0))
        [.dec "m" (n 0),
         .while (eLt (v "m") (n 8))
           [.ite (ne (eAnd (v "wd") (.loadw 1 (eAdd (atOff (v "a") aMask) (eMul (v "m") (n 8)))))
                (n 0))
              [.dec "j" (eMul (v "m") (n 8)),
               .while (eLt (v "j") (eAdd (eMul (v "m") (n 8)) (n 8)))
                 [.ite (ne (eAnd (v "wd") (pow (v "j"))) (n 0))
                    [.dec "x" (eAdd (eMul (v "w") (n 64)) (v "j")),
                     .ite (eLt (v "x") (v "nn")) body []] [],
                  inc "j"]] [],
            inc "m"]] [],
      inc "w"]]

/-- The start of a function given the slots `ps`: the area, each slot checked and made an address,
and with `len` the input's length checked. -/
def prologue (m : Mutant) (ofs : Nat) (ps : List (String × String)) (len : Bool := false) :
    List PStmt :=
  [areaAt ofs] ++
  ps.flatMap (fun (x, p) => (if m == .unchecked then [] else [kept x (slots - 1)]) ++ [.dec p (slot x)]) ++
  (if len then [.dec "nn" (word (v "a") aLen), kept "nn" inputMax] else [])

/-- The end of a function that built the set at `q`: its window stored. -/
def epilogue : List PStmt :=
  [.store (atOff (v "q") sLo) (v "dl"), .store (atOff (v "q") sHi) (v "dh"), .ret (n 0)]

/-- The set at `q` emptied: the words of its window cleared. -/
def clearQ : List PStmt :=
  [.dec "cl" (word (v "q") sLo), kept "cl" (setWords - 1),
   .dec "ch" (word (v "q") sHi), kept "ch" (setWords - 1),
   .dec "cw" (v "cl"),
   .while (eLe (v "cw") (v "ch")) [.store (bitWord "q" (v "cw")) (n 0), inc "cw"],
   .store (atOff (v "q") sLo) (n 1), .store (atOff (v "q") sHi) (n 0)]

/-! ## The operations on sets -/

section
variable (m : Mutant) (ofs : Nat)

def setClear : PFun :=
  { name := "setClear", params := [(1, "d")], body :=
    prologue m ofs [("d", "q")] ++ clearQ ++ [.ret (n 0)] }

/-- The set `d` given position `y` too. -/
def setAdd : PFun :=
  { name := "setAdd", params := [(1, "d"), (1, "y")], body :=
    prologue m ofs [("d", "q")] ++
    [kept "y" inputMax, .dec "yw" (.shr (v "y") (n 6)), kept "yw" (setWords - 1),
     .dec "yj" (eAnd (v "y") (n 63)),
     .store (bitWord "q" (v "yw")) (eOr (.loadw 1 (bitWord "q" (v "yw"))) (pow (v "yj"))),
     .dec "dl" (word (v "q") sLo), .dec "dh" (word (v "q") sHi),
     .ite (eLt (v "dh") (v "dl"))
       [.store (atOff (v "q") sLo) (v "yw"), .store (atOff (v "q") sHi) (v "yw")]
       [.ite (eLt (v "yw") (v "dl")) [.store (atOff (v "q") sLo) (v "yw")] [],
        .ite (eLt (v "dh") (v "yw")) [.store (atOff (v "q") sHi) (v "yw")] []],
     .ret (n 0)] }

/-- The set `d` given the positions of `s` too. -/
def setUnion : PFun :=
  { name := "setUnion", params := [(1, "d"), (1, "s")], body :=
    prologue m ofs [("d", "q"), ("s", "p")] ++
    [.dec "lo" (word (v "p") sLo), kept "lo" (setWords - 1),
     .dec "hi" (word (v "p") sHi), kept "hi" (setWords - 1),
     .dec "dl" (word (v "q") sLo), kept "dl" (setWords - 1),
     .dec "dh" (word (v "q") sHi), kept "dh" (setWords - 1),
     .ite (eLe (v "lo") (v "hi"))
       [.dec "w" (v "lo"),
        .while (eLe (v "w") (v "hi"))
          [.store (bitWord "q" (v "w"))
             (eOr (.loadw 1 (bitWord "q" (v "w"))) (.loadw 1 (bitWord "p" (v "w")))), inc "w"],
        .ite (eLt (v "dh") (v "dl"))
          [.store (atOff (v "q") sLo) (v "lo"), .store (atOff (v "q") sHi) (v "hi")]
          [.ite (eAnd (eLt (v "lo") (v "dl")) (n (if m == .unionWindow then 0 else 1)))
             [.store (atOff (v "q") sLo) (v "lo")] [],
           .ite (eLt (v "dh") (v "hi")) [.store (atOff (v "q") sHi) (v "hi")] []]] [],
     .ret (n 0)] }

/-- The set `s` copied into `d`, another slot. -/
def setCopy : PFun :=
  { name := "setCopy", params := [(1, "d"), (1, "s")], body :=
    prologue m ofs [("d", "q"), ("s", "p")] ++ clearQ ++
    [.dec "lo" (word (v "p") sLo), kept "lo" (setWords - 1),
     .dec "hi" (word (v "p") sHi), kept "hi" (setWords - 1),
     .dec "w" (v "lo"),
     .while (eLe (v "w") (v "hi")) [.store (bitWord "q" (v "w")) (.loadw 1 (bitWord "p" (v "w"))), inc "w"],
     .store (atOff (v "q") sLo) (v "lo"), .store (atOff (v "q") sHi) (v "hi"), .ret (n 0)] }

/-- 1, and `d` emptied, when the set `s` is empty; 0 when it is not. -/
def setVoid : PFun :=
  { name := "setVoid", params := [(1, "s"), (1, "d")], body :=
    prologue m ofs [("s", "p"), ("d", "q")] ++
    [.ite (eLt (word (v "p") sHi) (word (v "p") sLo)) (clearQ ++ [.ret (n 1)]) [.ret (n 0)]] }

/-- The set `d` without the positions of `s`, its window cut to the words still holding one. -/
def setMinus : PFun :=
  { name := "setMinus", params := [(1, "d"), (1, "s")], body :=
    prologue m ofs [("d", "q"), ("s", "p")] ++
    [.dec "lo" (word (v "q") sLo), kept "lo" (setWords - 1),
     .dec "hi" (word (v "q") sHi), kept "hi" (setWords - 1),
     .dec "w" (v "lo"),
     .while (eLe (v "w") (v "hi"))
       [.store (bitWord "q" (v "w"))
          (eAnd (.loadw 1 (bitWord "q" (v "w"))) (eXor (.loadw 1 (bitWord "p" (v "w"))) (n all1))),
        inc "w"],
     .dec "go" (n 1),
     .while (v "go")
       [.ite (eLe (v "lo") (v "hi"))
          [.ite (eEq (.loadw 1 (bitWord "q" (v "lo"))) (n 0)) [inc "lo"] [.assign "go" (n 0)]]
          [.assign "go" (n 0)]],
     .assign "go" (n 1),
     .while (v "go")
       [.ite (eLe (v "lo") (v "hi"))
          [.ite (eEq (.loadw 1 (bitWord "q" (v "hi"))) (n 0))
             [.assign "hi" (eSub (v "hi") (n 1))] [.assign "go" (n 0)]]
          [.assign "go" (n 0)]],
     .ite (eLt (v "hi") (v "lo"))
       [.store (atOff (v "q") sLo) (n 1), .store (atOff (v "q") sHi) (n 0)]
       [.store (atOff (v "q") sLo) (v "lo"), .store (atOff (v "q") sHi) (v "hi")],
     .ret (n 0)] }

/-- The set `x` without the positions of `d`, and `d` given them: one round's new positions. -/
def setGrow : PFun :=
  { name := "setGrow", params := [(1, "x"), (1, "d")], body :=
    [.call "c" "setMinus" [v "x", v "d"], .call "u" "setUnion" [v "d", v "x"], .ret (n 0)] }

/-- Whether the set `s` is empty: 1 if it is. -/
def setEmpty : PFun :=
  { name := "setEmpty", params := [(1, "s")], body :=
    prologue m ofs [("s", "p")] ++
    [.dec "lo" (word (v "p") sLo), .dec "hi" (word (v "p") sHi),
     .ite (eLt (v "hi") (v "lo")) [.ret (n 1)] [.ret (n 0)]] }

/-- Whether the set `s` holds position `y`: 1 if it does. -/
def setHas : PFun :=
  { name := "setHas", params := [(1, "s"), (1, "y")], body :=
    prologue m ofs [("s", "p")] ++
    [kept "y" inputMax, .dec "yw" (.shr (v "y") (n 6)), kept "yw" (setWords - 1),
     .dec "yj" (eAnd (v "y") (n 63)),
     .ret (ne (eAnd (.loadw 1 (bitWord "p" (v "yw"))) (pow (v "yj"))) (n 0))] }

/-- The positions one past those of `s` whose byte is in class `k`, into `d`. -/
def leafClass : PFun :=
  { name := "leafClass", params := [(1, "s"), (1, "d"), (1, "k")], body :=
    prologue m ofs [("s", "p"), ("d", "q")] true ++ clearQ ++
    [kept "k" (classes.length - 1),
     .dec "t" (eAdd (atOff (v "a") aClass) (eMul (v "k") (n 32))),
     .dec "dl" (n 1), .dec "dh" (n 0), .dec "df" (n 1)] ++
    eachPos
      [.dec "b" (byte (eAdd (atOff (v "a") aInput) (v "x"))),
       .dec "bw" (eAdd (eAdd (eLe (n 64) (v "b")) (eLe (n 128) (v "b"))) (eLe (n 192) (v "b"))),
       .ite (ne (eAnd (.loadw 1 (eAdd (v "t") (eMul (v "bw") (n 8)))) (pow (eAnd (v "b") (n 63))))
           (n 0))
         (addBit m (eAdd (v "x") (n 1))) []] ++
    epilogue }

/-- The positions past string `k` from those of `s` where it lies, into `d`. -/
def leafText : PFun :=
  { name := "leafText", params := [(1, "s"), (1, "d"), (1, "k")], body :=
    prologue m ofs [("s", "p"), ("d", "q")] true ++ clearQ ++
    [kept "k" (texts.length - 1),
     .dec "t" (eAdd (atOff (v "a") aTexts) (eMul (v "k") (n 24))),
     .dec "off" (word (v "t") 0), kept "off" textBytes,
     .dec "len" (word (v "t") 8), kept "len" textMax,
     .dec "cf" (word (v "t") 16), kept "cf" 1,
     .dec "dl" (n 1), .dec "dh" (n 0), .dec "df" (n 1)] ++
    eachPos
      [.ite (eLe (eAdd (v "x") (v "len")) (v "nn"))
        [.dec "ok" (n 1), .dec "i" (n 0),
         .while (eLt (v "i") (v "len"))
           [.dec "b" (byte (eAdd (eAdd (atOff (v "a") aInput) (v "x")) (v "i"))),
            .dec "lb" (eAdd (v "b") (eMul (n 32)
              (eAnd (n (if m == .caseful then 0 else 1))
                (eAnd (v "cf") (eAnd (eLe (n 65) (v "b")) (eLe (v "b") (n 90))))))),
            .ite (ne (v "lb") (byte (eAdd (eAdd (atOff (v "a") aTextBytes) (v "off")) (v "i"))))
              [.assign "ok" (n 0)] [],
            inc "i"],
         .ite (v "ok") (addBit m (eAdd (v "x") (v "len"))) []] []] ++
    epilogue }

/-- Whether the byte in the local `b` is in the class of rule `r`, which is one. -/
def inClass (r : String) (b : PExpr) : PExpr :=
  match classOf steps (termOf (ruleIndex r)) with
  | some rs => (rs.map fun (lo, hi) => eAnd (eLe (n lo) b) (eLe b (n hi))).foldl eOr (n 0)
  | none => n 0

/-- Where each comment of the positions of `s` ends, into `d`: `(`, then text, quoted pairs,
comments and white space that folds at most once between two of them, to the `)` that closes it.
The state: 0 after `(` or a part, 1 in white space, 2 just after its CRLF, 3 in white space after
it. -/
def ruleComment : PFun :=
  let wsp := inClass "wsp" (v "b")
  let at1 := byte (eAdd (eAdd (atOff (v "a") aInput) (v "y")) (n 1))
  let more := eLt (eAdd (v "y") (n 1)) (v "nn")
  { name := "ruleComment", params := [(1, "s"), (1, "d")], body :=
    prologue m ofs [("s", "p"), ("d", "q")] true ++ clearQ ++
    [.dec "dl" (n 1), .dec "dh" (n 0), .dec "df" (n 1)] ++
    eachPos
      [.ite (eEq (byte (eAdd (atOff (v "a") aInput) (v "x"))) (n 40))
        [.dec "y" (eAdd (v "x") (n 1)), .dec "dep" (n 1), .dec "sm" (n 0), .dec "go" (n 1),
         .while (eEq (v "go") (n 1))
           [.ite (eLt (v "y") (v "nn"))
             [.dec "b" (byte (eAdd (atOff (v "a") aInput) (v "y"))),
              .ite (eEq (v "sm") (n 2))
                [.ite wsp [.assign "sm" (n 3), inc "y"] [.assign "go" (n 0)]]
                [.ite wsp [.ite (eEq (v "sm") (n 0)) [.assign "sm" (n 1)] [], inc "y"]
                  [.ite (eEq (v "b") (n 13))
                    [.ite (eAnd (eEq (v "sm") (n 3)) (n (if m == .commentFold then 0 else 1)))
                      [.assign "go" (n 0)]
                      [.ite (eAnd more (eEq at1 (n 10)))
                        [.assign "sm" (n 2), .assign "y" (eAdd (v "y") (n 2))]
                        [.assign "go" (n 0)]]]
                    [.ite (or2 (inClass "ctext" (v "b"))
                        (eAnd (eEq (v "b") (n 92)) (n (if m == .commentEscape then 1 else 0))))
                      [.assign "sm" (n 0), inc "y"]
                      [.ite (eEq (v "b") (n 92))
                        [.ite (eAnd more (or2 (inClass "vchar" at1) (inClass "wsp" at1)))
                          [.assign "sm" (n 0), .assign "y" (eAdd (v "y") (n 2))]
                          [.assign "go" (n 0)]]
                        [.ite (eEq (v "b") (n 40))
                          [inc "dep", .assign "sm" (n 0), inc "y"]
                          [.ite (eEq (v "b") (n 41))
                            [.assign "dep" (eSub (v "dep") (n 1)), .assign "sm" (n 0), inc "y",
                             .ite (eEq (v "dep") (n 0)) [.assign "go" (n 2)] []]
                            [.assign "go" (n 0)]]]]]]]]
             [.assign "go" (n 0)]],
         .ite (eEq (v "go") (n 2)) (addBit m (v "y")) []] []] ++
    epilogue }

end

/-! ## The rules' functions -/

def funName (i : Nat) : String :=
  if i == commentRule then "ruleComment"
  else "rule_" ++ String.ofList ((names[i]?.getD "").toList.map fun c => if c == '-' then '_' else c)

def classIndex (b : List Nat) : Nat := (classes.findIdx? (· == b)).getD 0
def textIndex (t : List Nat × Bool) : Nat := (texts.findIdx? (· == t)).getD 0

/-- The call that reads leaf `l` from slot `s` into slot `d`, its result named `c`. -/
def leafCall (c : String) (l : Leaf) (s d : PExpr) : PStmt :=
  match l with
  | .cls b => .call c "leafClass" [s, d, n (classIndex b)]
  | .text bs cl => .call c "leafText" [s, d, n (textIndex (bs, cl))]

section
variable (m : Mutant)

/-- Statements that put into slot `d` the ends of the matches of `t` from the positions in slot
`s`, with the slots from `free` on for their own sets; `k` numbers their locals. -/
def gen : Nat → Term → PExpr → PExpr → Nat → Nat → List PStmt × Nat
  | 0, _, _, _, _, k => ([], k)
  | f + 1, t, s, d, free, k =>
    let c := s!"c{k}"
    match leafOf t with
    | some l => ([leafCall c l s d], k + 1)
    | none =>
      match t with
      | .ref i => ([.call c (funName i) [s, d]], k + 1)
      | .seq [] => ([.call c "setCopy" [d, s]], k + 1)
      | .seq [u] => gen f u s d free k
      | .seq (u :: us) =>
        -- Each result but the last into one of two slots in turn; an empty one ends the sequence
        -- with none.
        let last := us.length
        let (out, _, k) := ((u :: us).zipIdx).foldr (fun (t, i) (rest, _, k) =>
          let src := if i == 0 then s else n (free + (i + 1) % 2)
          let dst := if i == last then d else n (free + i % 2)
          let (b, k) := gen f t src dst (free + 2) k
          let tail := if i == last then [] else
            [.call s!"e{k}" "setVoid" [dst, d], .ite (v s!"e{k}") [] rest]
          (b ++ tail, src, k + 1)) (([] : List PStmt), s, k)
        (out, k)
      | .alt [] => ([.call c "setClear" [d]], k + 1)
      | .alt [u] => gen f u s d free k
      | .alt (u :: us) =>
        let us := if m == .altLast then us.dropLast else us
        let (first, k) := gen f u s d (free + 1) k
        us.foldl (fun (acc, k) u =>
          let (b, k) := gen f u s (n free) (free + 1) k
          (acc ++ b ++ [.call s!"c{k}" "setUnion" [d, n free]], k + 1)) (first, k)
      | .rep 0 (some 1) u =>
        let (b, k) := gen f u s d free k
        (b ++ [.call s!"c{k}" "setUnion" [d, s]], k + 1)
      | .rep lo hi u =>
        -- As `endsFrom`: from the frontier, the positions the last round reached that were not
        -- reached before, a round more, while the bound allows and a round reaches any; from
        -- round `lo` on, what a round reaches counts. The rounds write two slots in turn, `fr`
        -- naming the frontier's and `nx` the next round's.
        let fr := s!"f{k}"
        let nx := s!"x{k}"
        let cnt := s!"n{k}"
        let go := s!"g{k}"
        let i := s!"i{k}"
        let e := s!"e{k}"
        let (body, k') := gen f u (v fr) (v nx) (free + 2) (k + 1)
        let stop : List PStmt := match hi with
          | some h => if m == .repPastBound then [] else
            [.ite (eLe (n h) (v cnt)) [.assign go (n 0)] []]
          | none => []
        ([if lo == 0 then .call s!"{c}b" "setCopy" [d, s] else .call s!"{c}b" "setClear" [d],
          .dec fr s, .dec nx (n free), .dec cnt (n 0), .dec go (n 1), .dec i (n 0),
          .while (eAnd (v go) (eLt (v i) (eAdd (v "nn") (n (lo + 1)))))
            (inc i :: stop ++
             [.ite (v go)
               (body ++ [inc cnt, .call e "setEmpty" [v nx],
                 .ite (v e) [.assign go (n 0)]
                   [.ite (eLt (v cnt) (n lo)) [] [.call s!"{c}d" "setGrow" [v nx, d]],
                    .assign fr (v nx),
                    .ite (eEq (v nx) (n free)) [.assign nx (n (free + 1))] [.assign nx (n free)]]])
               []])], k')
      | _ => ([.call c "setClear" [d]], k + 1)

/-- Whether a term's statements read the input's length, which bounds a repetition. -/
def repeats : Nat → Term → Bool
  | 0, _ => false
  | f + 1, t =>
    if (leafOf t).isSome then false else
    match t with
    | .seq ts | .alt ts => ts.any (repeats f)
    | .rep 0 (some 1) u => repeats f u
    | .rep _ _ _ => true
    | _ => false

/-- Rule `i`'s function, its frame at `frameOf i`. -/
def ruleFun (ofs : Nat) (i : Nat) : PFun :=
  if i == commentRule then ruleComment m ofs
  else
    { name := funName i, params := [(1, "s"), (1, "d")], body :=
      [.call "e" "setVoid" [v "s", v "d"], .ite (v "e") [.ret (n 0)] []] ++
      (if repeats steps (termOf i) then [areaAt ofs, .dec "nn" (word (v "a") aLen)] else []) ++
      (gen m steps (termOf i) (v "s") (v "d") (frameOf i) 0).1 ++ [.ret (n 0)] }

/-! ## The program -/

/-- The words that set the area up: the powers of two, every slot empty, the classes and the
strings. -/
def tables (ofs : Nat) : PFun :=
  let classWords := classes.zipIdx.flatMap fun (b, k) =>
    b.zipIdx.map fun (w, j) => PStmt.store (atOff (v "a") (aClass + 32 * k + 8 * j)) (n w)
  let starts := (texts.map (·.1.length)).foldl (fun acc l => acc ++ [acc.getLast?.getD 0 + l]) [0]
  let textWords := (texts.zip starts).zipIdx.flatMap fun (((bs, cl), o), k) =>
    [PStmt.store (atOff (v "a") (aTexts + 24 * k)) (n o),
     .store (atOff (v "a") (aTexts + 24 * k + 8)) (n bs.length),
     .store (atOff (v "a") (aTexts + 24 * k + 16)) (n (if cl then 1 else 0))] ++
    bs.zipIdx.map fun (b, j) => PStmt.storeb (atOff (v "a") (aTextBytes + o + j)) (n b)
  { name := "tables", body :=
    [areaAt ofs, .store (atOff (v "a") aPow) (n 1), .dec "j" (n 1),
     .while (eLt (v "j") (n 64))
       [.dec "h" (.loadw 1 (eAdd (atOff (v "a") aPow) (eMul (eSub (v "j") (n 1)) (n 8)))),
        .store (eAdd (atOff (v "a") aPow) (eMul (v "j") (n 8))) (eAdd (v "h") (v "h")), inc "j"],
     -- Every slot empty, every bit clear: the heap may hold anything at the start.
     .dec "k" (n 0),
     .while (eLt (v "k") (n slots))
       [.dec "q" (slot "k"), .store (atOff (v "q") sLo) (n 1), .store (atOff (v "q") sHi) (n 0),
        .dec "w" (n 0),
        .while (eLt (v "w") (n setWords)) [.store (bitWord "q" (v "w")) (n 0), inc "w"], inc "k"]] ++
    (List.range 8).map (fun m => PStmt.store (atOff (v "a") (aMask + 8 * m)) (n (255 * 2 ^ (8 * m)))) ++
    classWords ++ textWords ++ [.ret (n 0)] }

/-- The call of rule `i` from slot 0 into slot 1. -/
def rootCall (i : Nat) : PStmt :=
  if hasFun i then .call "c" (funName i) [n 0, n 1]
  else match leafOf (termOf i) with
    | some l => leafCall "c" l (n 0) (n 1)
    | none => .call "c" "setClear" [n 1]

/-- Every function but `main`, each after those it calls. -/
def functions (ofs : Nat) : List PFun :=
  [setClear m ofs, setAdd m ofs, setUnion m ofs, setCopy m ofs, setVoid m ofs, setMinus m ofs,
   setGrow, setEmpty m ofs, setHas m ofs, leafClass m ofs, leafText m ofs, tables ofs] ++
  order.map (ruleFun m ofs)

/-- A program that answers, for each case its host hands it, whether a match of the rule asked from
one of the positions given ends at the input's end: 1 if one does, 0 if not, 2 if the case is out of
range or a check failed. -/
def main (ofs : Nat) : PFun :=
  { name := "main", body :=
    [areaAt ofs, .call "t" "tables" [],
     .while (n 1)
       [.ffi "dn_next" [v "a", n 8, v "a", n size],
        .store (atOff (v "a") aBroken) (n 0),
        .dec "r" (word (v "a") aRule), .dec "nn" (word (v "a") aLen), .dec "ans" (n 2),
        .ite (or2 (or2 (eLt (v "nn") (n 0)) (eLt (n inputMax) (v "nn")))
            (or2 (eLt (v "r") (n 0)) (eLt (n (grammar.size - 1)) (v "r")))) []
          ([.call "z" "setClear" [n 0], .dec "k" (n 0), .dec "ks" (word (v "a") aStarts),
            .while (eAnd (eLt (v "k") (v "ks")) (eLt (v "k") (n startsMax)))
              [.call "u" "setAdd" [n 0, .loadw 1 (eAdd (atOff (v "a") aStartList) (eMul (v "k") (n 8)))],
               inc "k"]] ++
           (List.range grammar.size).map (fun i => .ite (eEq (v "r") (n i)) [rootCall i] []) ++
           [.call "h" "setHas" [n 1, v "nn"], .assign "ans" (v "h"),
            .ite (word (v "a") aBroken) [.assign "ans" (n 2)] []]),
        .store (atOff (v "a") aAnswer) (v "ans")],
     .ret (n 0)] }

end

/-- Where the area lies in the program the lane runs and the analysis reads: above the heap's
header. -/
def areaOffset : Nat := 64

/-- The heap the program needs: the header, then the area. -/
def heapSize : Nat := areaOffset + size

def program (m : Mutant := .none) : List PFun × PFun := (functions m areaOffset, main areaOffset)

/-- The area as a C header for the lane's host. -/
def header : String :=
  let defs : List (String × Nat) :=
    [("AT", areaOffset), ("RULE", aRule), ("LEN", aLen), ("ANSWER", aAnswer), ("INPUT", aInput),
     ("INPUT_MAX", inputMax), ("STARTS", aStarts), ("START_LIST", aStartList),
     ("STARTS_MAX", startsMax), ("AREA", size), ("RULES", grammar.size)]
  "/* Generated by dn-compiler emit-grammar-layout from DN.News.AbnfProg. */\n" ++
  "#ifndef DN_GRAMMAR_LAYOUT_H\n#define DN_GRAMMAR_LAYOUT_H\n" ++
  String.join (defs.map fun (name, value) => s!"#define DN_GRAMMAR_{name} {value}\n") ++
  "#endif\n"

/-- Whether the analysis of decision 0004 accepts the program, its heap the header and the area. -/
def accepted (m : Mutant) : Bool :=
  let (fs, f) := program m
  match fs.mapM (fun g => (Lower.lower g).map (g.name, g.params.map (·.2), ·)), Lower.lower f with
  | some fns, some p => (Analyzer.checkProgram heapSize fns p).toBool
  | _, _ => false

/-- Each function calls only those before it. -/
def regression_957 : Bool := ordered

/-- The analysis accepts the program, and refuses it when the functions do not check their slots. -/
def regression_958 (_ : Unit) : Bool := accepted .none && !accepted .unchecked

/-- Every string a leaf matches is of one byte at least and of at most `textMax`, and there is a
class and a string: `eachPos` and the strings' table rest on it. -/
def regression_959 : Bool :=
  texts.all (fun (bs, _) => 1 ≤ bs.length && bs.length ≤ textMax) && !classes.isEmpty && !texts.isEmpty

/-- The rules the comment's scan names are the grammar's, and those it reads as classes are. -/
def regression_960 : Bool :=
  names[commentRule]? == some "comment" &&
    ["wsp", "ctext", "vchar"].all fun r => names.contains r && (classOf steps (termOf (ruleIndex r))).isSome

end DN.News.AbnfProg
