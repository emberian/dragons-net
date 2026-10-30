-- SPDX-License-Identifier: AGPL-3.0-or-later
import Lean.Data.Json
import DN.Compiler.Keywords

/-!
# DN.Compiler.Parse

CakeML's parser of Pancake at `ed31510` written again in Lean, for the programs the gate prints:
the lexer of `pancake/parser/panLexerScript.sml`, the statements and expressions of
`panPEGScript.sml` as its PEG tries them, choice by choice, and the tree
`panPtreeConversionScript.sml` builds of what it read, places left out, its names localised as
`localise_topdecs` does. A token the gate never prints is refused, and with it every level and
form of the grammar that needs one. So is a form that printed tokens make but the gate never
prints: a structure, a call other than `var r = f(..)`, `__add_with_carry__`, a shape other than
one word. `scripts/check_parse.sh` holds the tree to the one CakeML's parser gives in HOL4 on every
printed program and every cell of the precedence table; that the two agree off those texts is not
shown.
-/

namespace DN.Compiler.Parse

/-! ## The lexer (`panLexer`) -/

/-- A token as `panLexer` has it, keywords and symbols by their text. -/
inductive Tok
  | int (n : Nat) | ident (s : String) | foreign (s : String) | kw (s : String) | sym (s : String)
  deriving DecidableEq, Repr

/-- The words `get_keyword` reads as keywords at `ed31510`, as the lexer's source lists them, and
the three with a leading `@`. -/
def keywords : List String :=
  ((Keywords.byRevision.lookup "ed31510b3b0d0523283b68ef7066882526d77df9").getD []) ++
    ["@base", "@biw", "@top"]

/-- The keywords and symbols the gate prints; the others are refused. -/
def printedKeywords : List String :=
  ["st", "st8", "if", "else", "while", "return", "var", "lds", "ld8", "@base", "fun", "export"]

def printedSymbols : List String :=
  ["&", "|", "^", "==", "<", "<=", "+", "-", "*", "<<", ">>>", "(", ")", ",", ";", "{", "}", "="]

/-- A word: a keyword, `@` and a foreign function's name, or a name. -/
def wordTok (s : String) : Option Tok :=
  if keywords.contains s then if printedKeywords.contains s then some (.kw s) else none
  else if s.front = '@' then if 2 ≤ s.length then some (.foreign (s.drop 1).toString) else none
  else some (.ident s)

def symTok (s : String) : Option Tok := if printedSymbols.contains s then some (.sym s) else none

/-- HOL's `isSpace`: a space, or a code from 9 to 13, the newline among them. -/
def isSpace (c : Char) : Bool := c = ' ' || (9 ≤ c.toNat && c.toNat ≤ 13)
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
def isWordRest (c : Char) : Bool := isAlpha c || isDigit c || c = '_'
def isSingleton (c : Char) : Bool := "+-^*().,;:[]{}".toList.contains c
def beginsGroup (c : Char) : Bool := "#=><!&|".toList.contains c
def inGroup (c : Char) : Bool := "=<>|&+".toList.contains c

/-- The longest prefix whose characters `p` takes, and the rest (`read_while`). -/
def readWhile (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then let r := readWhile p cs; (c :: r.1, r.2) else ([], c :: cs)

theorem readWhile_rest_le (p : Char → Bool) : ∀ cs, (readWhile p cs).2.length ≤ cs.length
  | [] => by simp [readWhile]
  | c :: cs => by
    unfold readWhile
    split
    · exact Nat.le_succ_of_le (readWhile_rest_le p cs)
    · exact Nat.le_refl _

def decimal (ds : List Char) : Nat := ds.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0

/-- The tokens of the text (`next_atom`, `token_of_atom`); none for an error, and for a negative
number, a comment or a token the gate never prints. -/
def lexChars : List Char → Option (List Tok)
  | [] => some []
  | c :: cs =>
    if isSpace c then lexChars cs
    else if isDigit c then
      return .int (decimal (c :: (readWhile isDigit cs).1)) :: (← lexChars (readWhile isDigit cs).2)
    else if c = '-' && (cs.head?.map isDigit).getD false then none
    else if c = '/' then none
    else if isSingleton c then return (← symTok (String.singleton c)) :: (← lexChars cs)
    else if beginsGroup c then
      return (← symTok (String.ofList (c :: (readWhile inGroup cs).1))) ::
        (← lexChars (readWhile inGroup cs).2)
    else if isAlpha c || c = '@' || c = '_' then
      return (← wordTok (String.ofList (c :: (readWhile isWordRest cs).1))) ::
        (← lexChars (readWhile isWordRest cs).2)
    else none
termination_by cs => cs.length
decreasing_by
  all_goals simp only [List.length_cons]
  all_goals first
    | omega
    | exact Nat.lt_succ_of_le (readWhile_rest_le _ _)

def lex (s : String) : Option (List Tok) := lexChars s.toList

/-! ## The tree (`panLang`, as `parse_topdecs_to_ast` gives it) -/

/-- An expression; words are their value below 2^64. -/
inductive Exp
  | const (w : Nat)
  | var («local» : Bool) (name : String)
  | base
  | op (o : String) (es : List Exp)
  | mul (es : List Exp)
  | cmp (c : String) (a b : Exp)
  | shift (s : String) (e : Exp) (n : Nat)
  | load (e : Exp) | loadByte (e : Exp)
  deriving Inhabited

inductive Prog
  | skip
  | dec (v : String) (e : Exp) (p : Prog)
  | assign («local» : Bool) (v : String) (e : Exp)
  | store (a e : Exp) | storeByte (a e : Exp)
  | seq (p q : Prog)
  | ite (e : Exp) (p q : Prog)
  | while (e : Exp) (p : Prog)
  | ret (e : Exp)
  | extCall (n : String) (a b c d : Exp)
  | decCall (v f : String) (args : List Exp) (p : Prog)
  deriving Inhabited

structure Func where
  name : String
  exported : Bool
  params : List String
  body : Prog

/-- `i2w`: a number as a 64-bit word. -/
def word (n : Nat) : Nat := n % 2 ^ 64

/-- `conv_binaryExps`: an operand joined to what came before, into its chain unless that is of
another operator or a subtraction, which takes two operands only. -/
def joined (o : String) (res e : Exp) : Exp :=
  match res with
  | .op b es => if b ≠ o || (b = "Sub" && es.length = 2) then .op o [res, e] else .op b (es ++ [e])
  | r => .op o [r, e]

/-- The comparison a printed symbol makes, and whether its operands swap (`conv_cmp`). -/
def cmpOf : String → Option (String × Bool)
  | "<" => some ("Less", false) | "<=" => some ("NotLess", true) | _ => none

def shiftOf : String → Option String
  | "<<" => some "Lsl" | ">>>" => some "Lsr" | _ => none

def comparison (c : String × Bool) (a b : Exp) : Exp := if c.2 then .cmp c.1 b a else .cmp c.1 a b

/-! ## The grammar (`pancake_peg`)

The levels of expressions as the PEG has them, from `EEqNT` down to `EBaseNT`, those of `||`, `&&`,
`ld32` and fields left out with their tokens; a repetition takes an operator only when an operand
follows it. `fuel` bounds the nesting, and running out refuses. -/

/-- `EEqNT`, under `ExpNT` and `EBoolAndNT`, which read one operand when no `||` or `&&` comes,
then `ECmpNT`, `ELoadNT`, `ELoadByteNT`, `EOrNT`, `EXorNT`, `EAndNT`, `EShiftNT`, `EAddNT`, `EMulNT`
and `EBaseNT`. -/
inductive Level
  | eq | cmp | lds | ld8 | or_ | xor | and_ | shift | add | mul | base
  deriving DecidableEq, Repr

/-- The level an operand of a level is read at. -/
def Level.next : Level → Level
  | .eq => .cmp | .cmp => .lds | .lds => .ld8 | .ld8 => .or_ | .or_ => .xor | .xor => .and_
  | .and_ => .shift | .shift => .add | .add => .mul | .mul => .base | .base => .base

/-- At a level of a chain, the tree an operator symbol makes of what came before and the next
operand (`conv_binaryExps`, and `Panop Mul`, which nests). -/
def step : Level → String → Option (Exp → Exp → Exp)
  | .or_, "|" => some (joined "Or")
  | .xor, "^" => some (joined "Xor")
  | .and_, "&" => some (joined "And")
  | .add, "+" => some (joined "Add")
  | .add, "-" => some (joined "Sub")
  | .mul, "*" => some fun res e => .mul [res, e]
  | _, _ => none

mutual
/-- An expression read at a level. -/
def pAt : Nat → Level → List Tok → Option (Exp × List Tok)
  | 0, _, _ => none
  | k + 1, l, ts =>
    match l with
    | .eq => do
      let (a, ts) ← pAt k .cmp ts
      match ts with
      | .sym "==" :: rest => match pAt k .cmp rest with
        | some (b, rest') => return (.cmp "Equal" a b, rest')
        | none => return (a, ts)
      | _ => return (a, ts)
    | .cmp => do
      let (a, ts) ← pAt k .lds ts
      match ts with
      | .sym s :: rest =>
        match cmpOf s with
        | some c => match pAt k .lds rest with
          | some (b, rest') => return (comparison c a b, rest')
          | none => return (a, ts)
        | none => return (a, ts)
      | _ => return (a, ts)
    | .lds =>
      match ts with
      | .kw "lds" :: .int 1 :: ts => do
        let (e, ts) ← pAt k .ld8 ts
        return (.load e, ts)
      | .kw "lds" :: _ => none
      | ts => pAt k .ld8 ts
    | .ld8 =>
      match ts with
      | .kw "ld8" :: ts => do
        let (e, ts) ← pAt k .or_ ts
        return (.loadByte e, ts)
      | ts => pAt k .or_ ts
    | .shift => do
      let (e, ts) ← pAt k .add ts
      shiftChain k e ts
    | .base =>
      match ts with
      | .sym "(" :: ts => do
        let (e, ts) ← pAt k .eq ts
        let .sym ")" :: rest := ts | none
        return (e, rest)
      | .kw "@base" :: rest => some (.base, rest)
      | .int n :: rest => some (.const (word n), rest)
      | .ident _ :: .sym "<" :: .ident _ :: .sym "=" :: _ => none
      | .ident v :: rest => some (.var false v, rest)
      | _ => none
    | l => do
      let (e, ts) ← pAt k l.next ts
      chain k l e ts
/-- The rest of a chain: while its operator and an operand follow. -/
def chain : Nat → Level → Exp → List Tok → Option (Exp × List Tok)
  | 0, _, _, _ => none
  | k + 1, l, res, .sym s :: ts =>
    match step l s with
    | some f => match pAt k l.next ts with
      | some (e, rest) => chain k l (f res e) rest
      | none => some (res, .sym s :: ts)
    | none => some (res, .sym s :: ts)
  | _ + 1, _, res, ts => some (res, ts)
/-- The shifts after an operand of `EShiftNT`, each by a number. -/
def shiftChain : Nat → Exp → List Tok → Option (Exp × List Tok)
  | 0, _, _ => none
  | k + 1, res, .sym s :: .int n :: ts =>
    match shiftOf s with
    | some sh => shiftChain k (.shift sh res n) ts
    | none => some (res, .sym s :: .int n :: ts)
  | _ + 1, res, ts => some (res, ts)
end

/-- An expression (`ExpNT`). -/
def pExp (k : Nat) (ts : List Tok) : Option (Exp × List Tok) := pAt k .eq ts

/-- Arguments: expressions apart by commas (`ArgListNT`), or none before the `)`. -/
def pArgs (k : Nat) (ts : List Tok) : Option (List Exp × List Tok) :=
  match ts with
  | .sym ")" :: _ => some ([], ts)
  | _ => do
    let (e, ts) ← pExp k ts
    let rec more : Nat → List Exp → List Tok → Option (List Exp × List Tok)
      | 0, _, _ => none
      | j + 1, es, .sym "," :: ts => match pExp k ts with
        | some (e, rest) => more j (es ++ [e]) rest
        | none => some (es, .sym "," :: ts)
      | _ + 1, es, ts => some (es, ts)
    more (ts.length + 1) [e] ts

/-- Whether `CallNT` or `RetCallNT` would read a call after `return` or a name and `=`: a function
or `*` comes next. -/
def callAhead : List Tok → Bool
  | .ident _ :: .sym "(" :: _ | .sym "*" :: _ => true
  | _ => false

/-- A statement of `StmtNT` that holds no block, as `conv_NonRecStmt` makes it. -/
def pStmt (k : Nat) : List Tok → Option (Prog × List Tok)
  | .ident v :: .sym "=" :: rest =>
    if callAhead rest then none
    else do
      let (e, rest) ← pExp k rest
      return (.assign false v e, rest)
  | .kw "st" :: ts => do
    let (a, ts) ← pExp k ts
    let .sym "," :: ts := ts | none
    let (e, ts) ← pExp k ts
    return (.store a e, ts)
  | .kw "st8" :: ts => do
    let (a, ts) ← pExp k ts
    let .sym "," :: ts := ts | none
    let (e, ts) ← pExp k ts
    return (.storeByte a e, ts)
  | .foreign n :: .sym "(" :: ts => do
    let (a, ts) ← pExp k ts
    let .sym "," :: ts := ts | none
    let (b, ts) ← pExp k ts
    let .sym "," :: ts := ts | none
    let (c, ts) ← pExp k ts
    let .sym "," :: ts := ts | none
    let (d, ts) ← pExp k ts
    let .sym ")" :: ts := ts | none
    return (.extCall n a b c d, ts)
  | .kw "return" :: rest =>
    if callAhead rest then none
    else do
      let (e, rest) ← pExp k rest
      return (.ret e, rest)
  | _ => none

/-- A declared name of one word: `ShapedIdentNT` with no shape before the name, or `1`. -/
def pShaped : List Tok → Option (String × List Tok)
  | .int 1 :: .ident v :: ts => some (v, ts)
  | .int _ :: _ => none
  | .ident _ :: .ident _ :: _ => none
  | .ident v :: ts => some (v, ts)
  | _ => none

mutual
/-- `ProgNT`: the statements of a block up to its `}`, none when the `}` comes at once; `try_ProgNT`
in `pTry`. -/
def pProg : Nat → List Tok → Option (Option Prog × List Tok)
  | 0, _ => none
  | k + 1, ts@(.kw "if" :: _) | k + 1, ts@(.kw "while" :: _) => do
    let (b, ts) ← pBlock k ts
    let (rest, ts) ← pProg k ts
    return (some (match rest with | some p => .seq b p | none => b), ts)
  | k + 1, .kw "var" :: ts => do
    let (v, ts) ← pShaped ts
    let .sym "=" :: ts := ts | none
    match ts with
    | .ident f :: .sym "(" :: args => do
      if f = "__add_with_carry__" then none
      let (es, args) ← pArgs k args
      let .sym ")" :: .sym ";" :: ts := args | none
      let (p, ts) ← pTry k ts
      return (some (.decCall v f es p), ts)
    | _ => do
      let (e, ts) ← pExp k ts
      let .sym ";" :: ts := ts | none
      let (p, ts) ← pTry k ts
      return (some (.dec v e p), ts)
  | _ + 1, .sym "}" :: ts => some (none, ts)
  | k + 1, .sym "{" :: ts => do
    let (p, ts) ← pTry k ts
    let .sym ";" :: ts := ts | none
    let (rest, ts) ← pProg k ts
    return (some (match rest with | some q => .seq p q | none => p), ts)
  | k + 1, ts => do
    let (s, ts) ← pStmt k ts
    let .sym ";" :: ts := ts | none
    let (rest, ts) ← pProg k ts
    return (some (match rest with | some q => .seq s q | none => s), ts)
/-- `try_ProgNT`: a block's statements, `skip` for an empty one. -/
def pTry : Nat → List Tok → Option (Prog × List Tok)
  | 0, _ => none
  | _ + 1, .sym "}" :: ts => some (.skip, ts)
  | k + 1, ts => do
    let (p, ts) ← pProg k ts
    return (p.getD .skip, ts)
/-- `IfNT` and `WhileNT`. -/
def pBlock : Nat → List Tok → Option (Prog × List Tok)
  | 0, _ => none
  | k + 1, .kw "if" :: ts => do
    let (e, ts) ← pExp k ts
    let .sym "{" :: ts := ts | none
    let (p, ts) ← pTry k ts
    match ts with
    | .kw "else" :: .sym "{" :: ts => do
      let (q, ts) ← pTry k ts
      return (.ite e p q, ts)
    | _ => return (.ite e p .skip, ts)
  | k + 1, .kw "while" :: ts => do
    let (e, ts) ← pExp k ts
    let .sym "{" :: ts := ts | none
    let (p, ts) ← pTry k ts
    return (.while e p, ts)
  | _, _ => none
end

/-! ## Names made local (`localise_topdecs`) -/

mutual
def localExp (ls : List String) : Exp → Exp
  | .var g v => .var (g || ls.contains v) v
  | .op o es => .op o (localExps ls es)
  | .mul es => .mul (localExps ls es)
  | .cmp c a b => .cmp c (localExp ls a) (localExp ls b)
  | .shift s e n => .shift s (localExp ls e) n
  | .load e => .load (localExp ls e)
  | .loadByte e => .loadByte (localExp ls e)
  | e => e
def localExps (ls : List String) : List Exp → List Exp
  | [] => []
  | e :: es => localExp ls e :: localExps ls es
end

def localProg (ls : List String) : Prog → Prog
  | .dec v e p => .dec v (localExp ls e) (localProg (v :: ls) p)
  | .assign g v e => .assign (g || ls.contains v) v (localExp ls e)
  | .store a e => .store (localExp ls a) (localExp ls e)
  | .storeByte a e => .storeByte (localExp ls a) (localExp ls e)
  | .seq p q => .seq (localProg ls p) (localProg ls q)
  | .ite e p q => .ite (localExp ls e) (localProg ls p) (localProg ls q)
  | .while e p => .while (localExp ls e) (localProg ls p)
  | .ret e => .ret (localExp ls e)
  | .extCall n a b c d => .extCall n (localExp ls a) (localExp ls b) (localExp ls c) (localExp ls d)
  | .decCall v f es p => .decCall v f (localExps ls es) (localProg (v :: ls) p)
  | p => p

/-! ## Functions (`TopDecListNT`, `FunNT`) -/

def pParams (ts : List Tok) : Option (List String × List Tok) :=
  match ts with
  | .sym ")" :: _ => some ([], ts)
  | _ => do
    let (p, ts) ← pShaped ts
    let rec more : Nat → List String → List Tok → Option (List String × List Tok)
      | 0, _, _ => none
      | j + 1, ps, .sym "," :: ts => match pShaped ts with
        | some (p, rest) => more j (ps ++ [p]) rest
        | none => some (ps, .sym "," :: ts)
      | _ + 1, ps, ts => some (ps, ts)
    more (ts.length + 1) [p] ts

def pFunc (k : Nat) : List Tok → Option (Func × List Tok)
  | ts => do
    let (exported, ts) := match ts with
      | .kw "export" :: rest => (true, rest)
      | rest => (false, rest)
    let .kw "fun" :: ts := ts | none
    let (name, ts) ← pShaped ts
    let .sym "(" :: ts := ts | none
    let (params, ts) ← pParams ts
    let .sym ")" :: .sym "{" :: ts := ts | none
    let (body, ts) ← pTry k ts
    return ({ name, exported, params, body := localProg params body }, ts)

/-- The functions of the tokens, every one of them read. -/
def pFuncs (k : Nat) : Nat → List Tok → Option (List Func)
  | _, [] => some []
  | 0, _ => none
  | j + 1, ts => do
    let (f, ts) ← pFunc k ts
    return f :: (← pFuncs k j ts)

/-- **The parser**: the functions of a text, as `parse_topdecs_to_ast` gives them, or none for
text it refuses or that is outside the subset. -/
def program (s : String) : Option (List Func) := do
  let ts ← lex s
  pFuncs (16 * ts.length + 16) (ts.length + 1) ts

/-! ## The tree as JSON, in the form of `backend/parser/dnParseShowLib.sml` -/

open Lean (Json)

def con (name : String) (args : List Json) : Json := .arr (#[.str name] ++ args.toArray)
def pan (name : String) (args : List Json := []) : Json := con s!"panLang${name}" args
def kind (l : Bool) : Json := pan (if l then "Local" else "Global")

def expJson : Exp → Json
  | .const w => pan "Const" [Lean.toJson w]
  | .var l v => pan "Var" [kind l, .str v]
  | .base => pan "BaseAddr"
  | .op o es => pan "Op" [con s!"asm${o}" [], .arr (es.map expJson).toArray]
  | .mul es => pan "Panop" [pan "Mul", .arr (es.map expJson).toArray]
  | .cmp c a b => pan "Cmp" [con s!"asm${c}" [], expJson a, expJson b]
  | .shift s e n => pan "Shift" [con s!"ast${s}" [], expJson e, Lean.toJson n]
  | .load e => pan "Load" [pan "One", expJson e]
  | .loadByte e => pan "LoadByte" [expJson e]

def progJson : Prog → Json
  | .skip => pan "Skip"
  | .dec v e p => pan "Dec" [.str v, pan "One", expJson e, progJson p]
  | .assign l v e => pan "Assign" [kind l, .str v, expJson e]
  | .store a e => pan "Store" [expJson a, expJson e]
  | .storeByte a e => pan "StoreByte" [expJson a, expJson e]
  | .seq p q => pan "Seq" [progJson p, progJson q]
  | .ite e p q => pan "If" [expJson e, progJson p, progJson q]
  | .while e p => pan "While" [expJson e, progJson p]
  | .ret e => pan "Return" [expJson e]
  | .extCall n a b c d => pan "ExtCall" [.str n, expJson a, expJson b, expJson c, expJson d]
  | .decCall v f es p => pan "DecCall" [.str v, pan "One", .str f, .arr (es.map expJson).toArray, progJson p]

def funcJson (f : Func) : Json :=
  pan "Function" [Json.mkObj [("name", .str f.name), ("inline", .bool false), ("export", .bool f.exported),
    ("params", .arr (f.params.map fun p => con "pair$," [.str p, pan "One"]).toArray),
    ("body", progJson f.body), ("return", pan "One")]]

/-- The program's functions as JSON, or `null` when the text is refused. -/
def programJson (s : String) : Json :=
  match program s with
  | some fs => .arr (fs.map funcJson).toArray
  | none => .null

end DN.Compiler.Parse
