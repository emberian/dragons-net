-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.Semantics

Adapted from the compiler extraction recorded in docs/provenance.json.
The model is a restricted 64-bit Pancake fragment; docs/pancake-semantics.md
records, clause by clause, the HOL4 definitions it was compared against and what
it leaves out. Correspondence to the pretty-printer/parser, ABI and executable is
tracked in docs/assurance.md.
-/

namespace DN.Compiler

/-- The machine word. The region `.pnk` fixes the 64-bit x64 target
(`(4294967295w:word64)` literal, C1 boundsChk_def). -/
abbrev Word := BitVec 64

/-! ## 1. Byte-level substrate (the faithfulness hot-spot)

Transcribed from HOL `byteScript.sml` / `alignmentScript.sml`. These are the
word/endian/byte choices C1 flagged as where "an off-by-a-sign-bit bug would
live". -/

/-- `byte_align w = align (LOG2 (dimindex(:64) DIV 8)) w = align 3 w`
(alignmentScript `byte_align_def`,`align_def`: `align 3` clears the low
`LOG2 8 = 3` address bits). On 64-bit that is masking off the low 3 bits. -/
def byteAlign (w : Word) : Word := w &&& (~~~ (7 : Word))

/-- `byte_index a be = if be then 8*((d-1) - w2n a MOD d) else 8*(w2n a MOD d)`
with `d = dimindex(:64) DIV 8 = 8` (byteScript `byte_index_def`). This is the
ENDIANNESS choice: big-endian counts bytes from the high end. -/
def byteIndex (a : Word) (be : Bool) : Nat :=
  let d := 8
  if be then 8 * ((d - 1) - (a.toNat % d)) else 8 * (a.toNat % d)

/-- `get_byte a w be = w2w (w >>> byte_index a be) : word8` (byteScript
`get_byte_def`). `>>>` is the logical (unsigned) shift `word_lsr`; `w2w` to
word8 is truncation to the low 8 bits (`setWidth 8`). -/
def getByte (a w : Word) (be : Bool) : BitVec 8 :=
  (w >>> (byteIndex a be)).setWidth 8

/-- `word_slice_alt hi lo w = FCP i. lo ≤ i < hi ∧ w ' i` (byteScript
`word_slice_alt_def`): keep bits `[lo,hi)` of `w`, zero elsewhere. -/
def wordSliceAlt (hi lo : Nat) (w : Word) : Word :=
  let low  := (1#64 <<< lo) - 1#64   -- bits [0,lo) set
  let high := (1#64 <<< hi) - 1#64   -- bits [0,hi) set
  w &&& (high &&& (~~~ low))

/-- `set_byte a b w be = word_slice_alt 64 (i+8) w || (w2w b << i) || word_slice_alt i 0 w`
with `i = byte_index a be` (byteScript `set_byte_def`): overwrite the 8 bits at
byte position `i` with `b`, keeping the rest of `w`. -/
def setByte (a : Word) (b : BitVec 8) (w : Word) (be : Bool) : Word :=
  let i := byteIndex a be
  wordSliceAlt 64 (i + 8) w ||| ((b.setWidth 64) <<< i) ||| wordSliceAlt i 0 w

/-! ## 2. Values, memory, FFI oracle, state -/

/-- The `ValWord` fragment of panSem `v` (region emits no structs, so this is
exact). `shape_of` of every such value is `One`. -/
abbrev Value := Word

/-- `ffi$ffi_outcome`. -/
inductive Outcome
  | failed
  | diverged
deriving Repr, DecidableEq

/-- `ffi$final_event`: the call that ended the run, with the bytes it was given. -/
structure FinalEvent where
  name : String
  conf : List (BitVec 8)
  array : List (BitVec 8)
  outcome : Outcome
deriving Repr, DecidableEq

/-- panSem `result` restricted to the ctors the region subset can produce or
propagate. -/
inductive Result
  | error
  | timeout
  | break_
  | continue_
  | return_ (v : Value)
  | finalFFI (outcome : FinalEvent)
deriving Repr, DecidableEq

/-- The result of one `call_FFI` (`ffi$ffi_result`): either terminate the whole
run (`FFI_final`) or return with a new ffi state + the bytes written back into
the array region (`FFI_return`). -/
inductive FFIResult (σ : Type)
  | final (event : FinalEvent)
  | ret   (newState : σ) (newBytes : List (BitVec 8))

/-- What an oracle answers (`ffi$oracle_result`): new state and bytes, or the
outcome that ends the run. -/
inductive OracleResult (σ : Type)
  | ret   (newState : σ) (newBytes : List (BitVec 8))
  | final (outcome : Outcome)

/-- The FFI oracle (`ffi$oracle`): the pre-existing FFI boundary, an explicit
trusted assumption. It answers with anything, including a reply of the wrong
length; `callFFI` is what turns such a reply into a failed call. -/
structure Oracle (σ : Type) where
  call : σ → String → List (BitVec 8) → List (BitVec 8) → OracleResult σ

/-- `call_FFI st (ExtCall name) conf array` (ffiScript `call_FFI_def`): the empty
name never reaches the oracle, and a reply whose length differs from the array
ends the run instead of being written. -/
def callFFI {σ : Type} (oracle : Oracle σ) (ffi : σ) (name : String)
    (conf array : List (BitVec 8)) : FFIResult σ :=
  if name = "" then .ret ffi array
  else
    match oracle.call ffi name conf array with
    | .ret newffi newBytes =>
      if newBytes.length = array.length then .ret newffi newBytes
      else .final ⟨name, conf, array, .failed⟩
    | .final outcome => .final ⟨name, conf, array, outcome⟩

/-- panSem `('a,'ffi) state`, restricted to the fields the region subset reads.
`locals` is the partial map `varname |-> v` (region uses only `Local`); `memory`
is `α word → α word_lab` (single-ctor `Word`, so `Word → Word`); `memaddrs` is
the address set as its `Bool` characteristic function. `globals/structs/code/
eshapes/sh_memaddrs/top_addr` are unused by the subset and omitted. -/
structure PancakeState (σ : Type) where
  locals   : String → Option Value
  memory   : Word → Word
  memaddrs : Word → Bool
  be       : Bool
  clock    : Nat
  ffi      : σ
  baseAddr : Word

variable {σ : Type}

/-- `mem_load_byte m dm be w` (panSem `mem_load_byte_def`): `case m (byte_align w)
of Word v => if byte_align w IN dm then SOME (get_byte w v be) else NONE`. The
single-ctor `Word v` match is definitional here. -/
def memLoadByte (m : Word → Word) (dm : Word → Bool) (be : Bool) (w : Word) :
    Option (BitVec 8) :=
  if dm (byteAlign w) then some (getByte w (m (byteAlign w)) be) else none

/-- `mem_store a w dm m = if addr IN dm then SOME ((addr =+ w) m) else NONE`
(panSem `mem_store_def`), used by `Store` via `mem_stores`/`flatten` on the
single-word value (`flatten (Val w) = [w]`). -/
def memStoreWord (m : Word → Word) (dm : Word → Bool) (addr w : Word) :
    Option (Word → Word) :=
  if dm addr then some (fun k => if k = addr then w else m k) else none

/-- `mem_store_byte m dm be w b` (panSem `mem_store_byte_def`). -/
def memStoreByte (m : Word → Word) (dm : Word → Bool) (be : Bool)
    (w : Word) (b : BitVec 8) : Option (Word → Word) :=
  if dm (byteAlign w)
  then some (fun k => if k = byteAlign w then setByte w b (m (byteAlign w)) be else m k)
  else none

/-- `read_bytearray a n get_byte` (miscScript `read_bytearray_def`): `a` is the
ADDRESS, `n` the COUNT; reads `n` successive bytes from `a`. -/
def readByteArray (m : Word → Word) (dm : Word → Bool) (be : Bool) :
    Word → Nat → Option (List (BitVec 8))
  | _, 0 => some []
  | a, n + 1 =>
    match memLoadByte m dm be a with
    | none => none
    | some b =>
      match readByteArray m dm be (a + 1) n with
      | none => none
      | some bs => some (b :: bs)

/-- `write_bytearray a bs m dm be` (panSem `write_bytearray_def`): writes the
tail at `a+1` first, then `b` at `a` (a right fold). A store out of range keeps
the memory this call was given, so the tail writes are dropped with it. -/
def writeByteArray (dm : Word → Bool) (be : Bool) :
    Word → List (BitVec 8) → (Word → Word) → (Word → Word)
  | _, [], m => m
  | a, b :: bs, m =>
    match memStoreByte (writeByteArray dm be (a + 1) bs m) dm be a b with
    | some m' => m'
    | none => m

/-! ## 3. Expression evaluation `eval : state → exp → Option Value`

Transcribed from panSem `eval_def`. `word_cmp Less` is SIGNED — this is C1's
trap, see §3.1. -/

/-- panLang `binop` subset used by the region (`asm$binop`), plus `sub` for the
fused-serve stages. `Sub` is the one binop panLang admits ONLY at arity 2
(`word_op Sub [w1;w2] = SOME (w1 - w2)`, `word_op_def`), so — unlike `Add`/`And`
— it carries no fold-identity specialisation delta: the model's binary `op .sub`
is exactly the source. -/
inductive Binop | add | and_ | sub
deriving Repr, DecidableEq

/-- panLang `cmp` subset (`asm$cmp`). `less` is `Cmp Less`, which `word_cmp Less
w1 w2 = (w1 < w2)` interprets as the SIGNED `word_lt` (asmScript `word_cmp_def`
:315). This is the P2 §4.2 seam that BITES for the comparison (C1-REPORT §2).
Modelled below with `BitVec.slt`.

`equal`/`notLess` are the two `cmp`s the fused-serve `==`/`<=` parse to
(panPtreeConversion `conv_cmp`): `word_cmp Equal w1 w2 = (w1 = w2)` and
`word_cmp NotLess w1 w2 = ¬(w1 < w2)` [SIGNED] (word_cmp_def). The parser emits
`a == b` as `Cmp Equal a b` and — SWAPPING operands — `a <= b` as
`Cmp NotLess b a` (`conv_cmp`: `LeqT ↦ (NotLess, swap=T)`); the swap is applied
in Lower.lean, so this model just needs the two comparators. -/
inductive Cmp | less | equal | notLess
deriving Repr, DecidableEq

/-- panLang `exp`, the region subset. `op`/`mul`/`cmp` are the arity-2
specialisations (see header delta note). -/
inductive PancakeExp
  | const    (w : Word)                       -- `Const w`
  | var      (name : String)                  -- `Var Local name`
  | base                                      -- `BaseAddr`
  | op       (bop : Binop) (l r : PancakeExp) -- `Op Add/And/Sub [l;r]`
  | mul      (l r : PancakeExp)               -- `Panop Mul [l;r]`
  | cmp      (c : Cmp) (l r : PancakeExp)     -- `Cmp Less/Equal/NotLess l r` (Less/NotLess SIGNED)
  | loadByte (addr : PancakeExp)              -- `LoadByte addr`
  | loadWord (addr : PancakeExp)              -- `Load One addr`
deriving Repr

/-- `word_cmp Less` = HOL `word_lt` = SIGNED comparison. In Lean `BitVec.slt` is
signed-less-than (`BitVec.<` / `<` would be UNSIGNED — the exact bug C1 warns of). -/
@[inline] def signedLt (a b : Word) : Bool := BitVec.slt a b

/-- `eval s e` (panSem `eval_def`), region subset. Total; returns `none` on the
panSem `NONE` cases (type mismatch, out-of-range load). -/
def eval (s : PancakeState σ) : PancakeExp → Option Value
  | .const w => some w                                   -- `eval s (Const w) = SOME (ValWord w)`
  | .var name => s.locals name                           -- `Var Local v = FLOOKUP s.locals v`
  | .base => some s.baseAddr                             -- `BaseAddr = SOME (ValWord s.base_addr)`
  | .op bop l r =>
    match eval s l, eval s r with
    | some a, some b =>
      match bop with
      | .add  => some (a + b)       -- `word_op Add [a;b] = FOLDR word_add 0w = a+b`
      | .and_ => some (a &&& b)     -- `word_op And [a;b] = FOLDR word_and (¬0w) = a&&&b`
      | .sub  => some (a - b)       -- `word_op Sub [a;b] = SOME (a - b)` (word_op_def, arity-2)
    | _, _ => none
  | .mul l r =>
    match eval s l, eval s r with
    | some a, some b => some (a * b)  -- `pan_op Mul [a;b] = SOME (a*b)` (pan_op_def)
    | _, _ => none
  | .cmp .less l r =>
    match eval s l, eval s r with
    -- `Cmp cmp e1 e2 = SOME (ValWord (if word_cmp cmp w1 w2 then 1w else 0w))`
    | some a, some b => some (if signedLt a b then 1 else 0)
    | _, _ => none
  | .cmp .equal l r =>
    match eval s l, eval s r with
    -- `word_cmp Equal w1 w2 = (w1 = w2)` (asmScript `word_cmp_def`)
    | some a, some b => some (if a = b then 1 else 0)
    | _, _ => none
  | .cmp .notLess l r =>
    match eval s l, eval s r with
    -- `word_cmp NotLess w1 w2 = ¬(w1 < w2)` [SIGNED] (asmScript `word_cmp_def`)
    | some a, some b => some (if signedLt a b then 0 else 1)
    | _, _ => none
  | .loadByte addr =>
    match eval s addr with
    -- `LoadByte addr`: mem_load_byte then `w2w` byte→word (zero-extend, setWidth 64)
    | some w =>
      match memLoadByte s.memory s.memaddrs s.be w with
      | some b => some (b.setWidth 64)
      | none => none
    | none => none
  | .loadWord addr =>
    match eval s addr with
    -- `Load One addr = if addr IN dm then SOME (Val (m addr)) else NONE` (mem_load_def, One)
    | some w => if s.memaddrs w then some (s.memory w) else none
    | none => none

/-! ### 3.2 Refinement lemmas for the fused-serve first-order ops

Each characterises `eval` of a newly-modelled op in terms of the underlying Lean
word operation it refines (`-`, word equality, signed `<`). These are the
non-vacuous obligations Lower.lean's totality on `POp.sub`/`eq`/`le` rests on:
whenever both operands evaluate, the op evaluates to exactly the word/bit result
of its `word_op_def`/`word_cmp_def` clause. -/

/-- `eval (Op Sub [l;r]) = SOME (a - b)` when `l ↦ a`, `r ↦ b` (`word_op Sub`). -/
theorem eval_sub (s : PancakeState σ) {l r : PancakeExp} {a b : Word}
    (hl : eval s l = some a) (hr : eval s r = some b) :
    eval s (.op .sub l r) = some (a - b) := by
  simp only [eval, hl, hr]

/-- `eval (Cmp Equal e1 e2) = SOME (if a = b then 1 else 0)` (`word_cmp Equal`). -/
theorem eval_equal (s : PancakeState σ) {l r : PancakeExp} {a b : Word}
    (hl : eval s l = some a) (hr : eval s r = some b) :
    eval s (.cmp .equal l r) = some (if a = b then 1 else 0) := by
  simp only [eval, hl, hr]

/-- `eval (Cmp NotLess e1 e2) = SOME (if a < b then 0 else 1)` [SIGNED `<`], i.e.
the indicator of `¬(a < b)` (`word_cmp NotLess`). Composed with Lower.lean's
operand swap this realises `a <= b`. -/
theorem eval_notLess (s : PancakeState σ) {l r : PancakeExp} {a b : Word}
    (hl : eval s l = some a) (hr : eval s r = some b) :
    eval s (.cmp .notLess l r) = some (if signedLt a b then 0 else 1) := by
  simp only [eval, hl, hr]

/-! ## 4. Program evaluation `evaluate : prog × state → result option × state`

Transcribed from panSem `evaluate_def`. Clocked big-step: `While`/`Call`
decrement the clock, `clock = 0` gives `TimeOut`. Termination is the panSem
lexicographic measure `(clock, sizeOf prog)` — see `termination_by` below.

The `fix_clock` clamp (panSem `fix_clock_def`) is INLINED at each loop/seq
recursive boundary as `min` on the returned clock: this is what makes the
well-founded recursion go through (the clamp bounds the recursive result's clock
UNCONDITIONALLY by `Nat.min_le_left`, exactly as panSem's `fix_clock_IMP_LESS_EQ`
supplies the decrease). -/

/-- panLang `prog`, the region subset. `dec` carries its continuation (panLang
`Dec v sh e prog` scopes over `prog`); a `.pnk` statement LIST lowers to a right
nest of `dec`/`seq` (see DN.Compiler/Lower.lean). -/
inductive PancakeProg
  | skip
  | dec     (v : String) (e : PancakeExp) (cont : PancakeProg)  -- `Dec v One e cont`
  | assign  (v : String) (e : PancakeExp)                       -- `Assign Local v e`
  | store   (dst src : PancakeExp)                              -- `Store dst src`
  | extCall (name : String) (confPtr confLen arrPtr arrLen : PancakeExp) -- `ExtCall …`
  | seq     (c1 c2 : PancakeProg)                               -- `Seq c1 c2`
  | cond    (e : PancakeExp) (c1 c2 : PancakeProg)              -- `If e c1 c2`
  | while_  (e : PancakeExp) (c : PancakeProg)                  -- `While e c`
  | ret     (e : PancakeExp)                                    -- `Return e`
  | storeByte (dst src : PancakeExp)                            -- `StoreByte dst src`
deriving Repr

/-- `FLOOKUP`-style update: `set_var v value s` writes `locals |+ (v,value)`. -/
def setLocal (lc : String → Option Value) (v : String) (val : Value) :
    String → Option Value :=
  fun k => if k = v then some val else lc k

/-- `res_var lc (v, old)` (panSem `res_var_def`): `old = NONE` deletes, `old =
SOME x` restores — both captured by writing the `Option` back at `v`. -/
def resVar (lc : String → Option Value) (v : String) (old : Option Value) :
    String → Option Value :=
  fun k => if k = v then old else lc k

/-- `empty_locals s` (panSem `empty_locals_def`). -/
def emptyLocals (s : PancakeState σ) : PancakeState σ :=
  { s with locals := fun _ => none }

/-- `dec_clock s` (panSem `dec_clock_def`). -/
def decClock (s : PancakeState σ) : PancakeState σ :=
  { s with clock := s.clock - 1 }

/-- The inlined `fix_clock old_s (res,new_s)` (panSem `fix_clock_def`): clamp the
returned clock to `min old.clock new.clock`. -/
def clampClock (old : Nat) (r : Option Result × PancakeState σ) :
    Option Result × PancakeState σ :=
  (r.1, { r.2 with clock := min old r.2.clock })

/-- `evaluate (prog, s)` (panSem `evaluate_def`), region subset. -/
def PancakeSem (oracle : Oracle σ) : PancakeProg → PancakeState σ →
    (Option Result × PancakeState σ)
  | .skip, s => (none, s)                                   -- `evaluate (Skip,s) = (NONE,s)`
  | .dec v e cont, s =>
    -- `Dec v sh e prog`: bind, run cont, restore old binding (`res_var`).
    -- shape check `sh = shape_of value` is vacuous (all region values are `One`).
    match eval s e with
    | some val =>
      let r := PancakeSem oracle cont { s with locals := setLocal s.locals v val }
      (r.1, { r.2 with locals := resVar r.2.locals v (s.locals v) })
    | none => (some .error, s)
  | .assign v e, s =>
    -- `Assign Local v src`: `is_valid_value` needs the variable to be bound already
    -- (the shape part is vacuous: every value is `One`).
    match eval s e, s.locals v with
    | some val, some _ => (none, { s with locals := setLocal s.locals v val })
    | _, _ => (some .error, s)
  | .store dst src, s =>
    -- `Store dst src`: eval both, `mem_stores addr (flatten value)` on one word.
    match eval s dst, eval s src with
    | some addr, some val =>
      match memStoreWord s.memory s.memaddrs addr val with
      | some m => (none, { s with memory := m })
      | none => (some .error, s)
    | _, _ => (some .error, s)
  | .extCall name cptr clen aptr alen, s =>
    -- `ExtCall`: read conf=[clen bytes @cptr] and arr=[alen bytes @aptr], hand them to
    -- `call_FFI`, and write the bytes it returns back @aptr. (panSem names the four
    -- evals sz1/ad1/sz2/ad2; `read_bytearray sz1 (w2n ad1)` = addr cptr, count clen.)
    match eval s cptr, eval s clen, eval s aptr, eval s alen with
    | some cp, some cl, some ap, some al =>
      match readByteArray s.memory s.memaddrs s.be cp cl.toNat,
            readByteArray s.memory s.memaddrs s.be ap al.toNat with
      | some conf, some arr =>
        match callFFI oracle s.ffi name conf arr with
        | .final event => (some (.finalFFI event), emptyLocals s)
        | .ret newffi newBytes =>
          (none, { s with memory := writeByteArray s.memaddrs s.be ap newBytes s.memory,
                          ffi := newffi })
      | _, _ => (some .error, s)
    | _, _, _, _ => (some .error, s)
  | .seq c1 c2, s =>
    -- `Seq c1 c2`: `let (res,s1) = fix_clock s (evaluate (c1,s))`; if NONE run c2.
    let r := clampClock s.clock (PancakeSem oracle c1 s)
    match r.1 with
    | none => PancakeSem oracle c2 r.2
    | some res => (some res, r.2)
  | .cond e c1 c2, s =>
    -- `If e c1 c2`: `evaluate (if w <> 0w then c1 else c2, s)`. False is 0w.
    match eval s e with
    | some w => PancakeSem oracle (if w ≠ 0 then c1 else c2) s
    | none => (some .error, s)
  | .while_ e c, s =>
    -- `While e c`: clocked loop. `w<>0w` continues; clock=0 → TimeOut.
    match eval s e with
    | some w =>
      if w ≠ 0 then
        if s.clock = 0 then (some .timeout, emptyLocals s)
        else
          let r := clampClock (s.clock - 1) (PancakeSem oracle c (decClock s))
          match r.1 with
          | some .continue_ => PancakeSem oracle (.while_ e c) r.2
          | none            => PancakeSem oracle (.while_ e c) r.2
          | some .break_    => (none, r.2)
          | some res        => (some res, r.2)
      else (none, s)
    | none => (some .error, s)
  | .ret e, s =>
    -- `Return e`: `size_of_shape (shape_of value) ≤ 32` is vacuous (One = size 1).
    match eval s e with
    | some v => (some (.return_ v), emptyLocals s)
    | none => (some .error, s)
  | .storeByte dst src, s =>
    -- `StoreByte dst src` (panSem `evaluate (StoreByte ...)` clause): both operands
    -- must evaluate to `ValWord`; store the LOW BYTE of the source word — panSem's
    -- `w2w value : word8`, i.e. truncation `setWidth 8` — at the destination address
    -- via `mem_store_byte`. Out-of-range store (`NONE`) raises `Error`.
    match eval s dst, eval s src with
    | some adr, some w =>
      match memStoreByte s.memory s.memaddrs s.be adr (w.setWidth 8) with
      | some m => (none, { s with memory := m })
      | none => (some .error, s)
    | _, _ => (some .error, s)
  termination_by prog s => (s.clock, sizeOf prog)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
        -- clock strictly decreases (While body via dec_clock, While recurse via clamp)
        | (apply Prod.Lex.left; simp only [clampClock, decClock]; omega)
        -- clock unchanged, size decreases (Dec cont, Seq c1, If chosen branch)
        | (apply Prod.Lex.right; (try split) <;> simp +arith)
        -- clamped clock (Seq c2): min s.clock _ ≤ s.clock, split eq/lt
        | (rw [Prod.lex_def]; simp only [clampClock];
           rcases Nat.eq_or_lt_of_le (Nat.min_le_left s.clock _) with h | h
           · exact Or.inr ⟨h, by simp +arith⟩
           · exact Or.inl h)

/-! ### 4.1 Refinement lemma for the byte store `StoreByte`

Characterises `evaluate (StoreByte dst src, s)` in terms of `mem_store_byte` on
the LOW BYTE of the source word (panSem's `w2w value`, i.e. `setWidth 8`):
whenever both operands evaluate and the byte-store is in range (`memStoreByte …
= some m`), the run raises NO result (`none`) and the post-state's memory IS the
byte-stored memory `m`, every other field of `s` unchanged. This is the
non-vacuous obligation that Lower.lean's lowering of `st8` (`PStmt.storeb`) to
`StoreByte` rests on: the conclusion pins the compiled post-state to the
`memStoreByte` image, not a `P → P` tautology. -/
theorem evaluate_storeByte (oracle : Oracle σ) (s : PancakeState σ)
    {dst src : PancakeExp} {adr w : Word} {m : Word → Word}
    (hd : eval s dst = some adr) (hs : eval s src = some w)
    (hm : memStoreByte s.memory s.memaddrs s.be adr (w.setWidth 8) = some m) :
    PancakeSem oracle (.storeByte dst src) s = (none, { s with memory := m }) := by
  simp only [PancakeSem, hd, hs, hm]

/-- The out-of-range companion: when the byte-store falls outside the address
domain (`memStoreByte … = none`), `StoreByte` raises `Error` and leaves the state
untouched (panSem's `NONE => (SOME Error, s)`). -/
theorem evaluate_storeByte_error (oracle : Oracle σ) (s : PancakeState σ)
    {dst src : PancakeExp} {adr w : Word}
    (hd : eval s dst = some adr) (hs : eval s src = some w)
    (hm : memStoreByte s.memory s.memaddrs s.be adr (w.setWidth 8) = none) :
    PancakeSem oracle (.storeByte dst src) s = (some .error, s) := by
  simp only [PancakeSem, hd, hs, hm]

/-! ### 4.2 The branches where the semantics stops

Each theorem pins a branch a permissive transcription would drop: the model must
refuse, not carry on. They are concrete instances, so they also witness that the
general lemmas above (`evaluate_storeByte_error` and its kind) are not vacuous. -/

/-- A state with nothing declared, to exercise the error branches. -/
def bareState (ffi : σ) : PancakeState σ :=
  { locals := fun _ => none, memory := fun _ => 0, memaddrs := fun _ => true,
    be := false, clock := 8, ffi := ffi, baseAddr := 0 }

/-- Reading a variable that was never declared has no value. -/
theorem eval_unbound_var_is_none (ffi : σ) : eval (bareState ffi) (.var "x") = none := rfl

/-- An operand without a value leaves the operator without one. -/
theorem eval_op_of_none (ffi : σ) :
    eval (bareState ffi) (.op .add (.var "x") (.const 1)) = none := rfl

/-- Loading a byte outside the memory domain has no value. -/
theorem eval_loadByte_outside_domain (ffi : σ) :
    eval { bareState ffi with memaddrs := fun _ => false } (.loadByte (.const 8)) = none := rfl

/-- Loading a word outside the memory domain has no value. -/
theorem eval_loadWord_outside_domain (ffi : σ) :
    eval { bareState ffi with memaddrs := fun _ => false } (.loadWord (.const 8)) = none := rfl

/-- A declaration whose initialiser has no value is an error. -/
theorem dec_without_value_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.dec "x" (.var "y") .skip) (bareState ffi) = (some .error, bareState ffi) := by
  simp only [PancakeSem, eval, bareState]

/-- Assigning to a variable that was never declared is an error. -/
theorem assign_unbound_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.assign "x" (.const 7)) (bareState ffi) = (some .error, bareState ffi) := by
  simp only [PancakeSem, eval, bareState]

/-- A word store outside the memory domain is an error, and the state is kept. -/
theorem store_outside_domain_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.store (.const 8) (.const 1))
        { bareState ffi with memaddrs := fun _ => false }
      = (some .error, { bareState ffi with memaddrs := fun _ => false }) := by
  simp [PancakeSem, eval, bareState, memStoreWord]

/-- So is a byte store outside the domain. -/
theorem storeByte_outside_domain_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.storeByte (.const 8) (.const 1))
        { bareState ffi with memaddrs := fun _ => false }
      = (some .error, { bareState ffi with memaddrs := fun _ => false }) := by
  simp [PancakeSem, eval, bareState, memStoreByte]

/-- A condition without a value is an error; neither branch runs. -/
theorem cond_without_value_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.cond (.var "x") .skip .skip) (bareState ffi)
      = (some .error, bareState ffi) := by
  simp only [PancakeSem, eval, bareState]

/-- A loop guard without a value is an error. -/
theorem while_without_value_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.while_ (.var "x") .skip) (bareState ffi)
      = (some .error, bareState ffi) := by
  simp only [PancakeSem, eval, bareState]

/-- A loop that still has work to do and no clock times out, and the locals go. -/
theorem while_out_of_clock_is_timeout (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.while_ (.const 1) .skip) { bareState ffi with clock := 0 }
      = (some .timeout, emptyLocals { bareState ffi with clock := 0 }) := by
  rw [PancakeSem]
  simp only [eval, bareState, ne_eq, show ((1 : Word) = 0) = False from by decide,
             not_false_eq_true, if_pos]

/-- A return without a value is an error. -/
theorem ret_without_value_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.ret (.var "x")) (bareState ffi) = (some .error, bareState ffi) := by
  simp only [PancakeSem, eval, bareState]

/-- An external call whose array is not readable is an error: the oracle is not reached. -/
theorem extCall_unreadable_array_is_error (ffi : σ) :
    PancakeSem ⟨fun st _ _ _ => .ret st []⟩ (.extCall "name" (.const 0) (.const 0) (.const 8) (.const 1))
        { bareState ffi with memaddrs := fun _ => false }
      = (some .error, { bareState ffi with memaddrs := fun _ => false }) := by
  simp [PancakeSem, eval, bareState, readByteArray, memLoadByte]

/-- An oracle that ends the run propagates as `FinalFFI`, and the locals go. -/
theorem extCall_final_propagates (ffi : σ) :
    PancakeSem ⟨fun _ _ _ _ => .final .diverged⟩
        (.extCall "name" (.const 0) (.const 0) (.const 8) (.const 0)) (bareState ffi)
      = (some (.finalFFI ⟨"name", [], [], .diverged⟩), emptyLocals (bareState ffi)) := by
  simp [PancakeSem, eval, bareState, readByteArray, callFFI, emptyLocals]

/-- An assignment whose right-hand side has no value is an error. -/
theorem assign_without_value_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.assign "x" (.var "y"))
        { bareState ffi with locals := fun k => if k = "x" then some 0 else none }
      = (some .error, { bareState ffi with locals := fun k => if k = "x" then some 0 else none }) := by
  simp [PancakeSem, eval, bareState]

/-- A word store whose address or value has no value is an error. -/
theorem store_without_value_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.store (.var "x") (.const 1)) (bareState ffi)
      = (some .error, bareState ffi) := by
  simp [PancakeSem, eval, bareState]

/-- The same for a byte store. -/
theorem storeByte_without_value_is_error (oracle : Oracle σ) (ffi : σ) :
    PancakeSem oracle (.storeByte (.var "x") (.const 1)) (bareState ffi)
      = (some .error, bareState ffi) := by
  simp [PancakeSem, eval, bareState]

/-- An external call whose pointers or lengths have no value is an error: the oracle
is not reached. -/
theorem extCall_without_value_is_error (ffi : σ) :
    PancakeSem ⟨fun st _ _ _ => .ret st []⟩
        (.extCall "name" (.var "x") (.const 0) (.const 8) (.const 0)) (bareState ffi)
      = (some .error, bareState ffi) := by
  simp [PancakeSem, eval, bareState]

/-- An external call whose configuration bytes cannot be read is an error, before the
array is touched. -/
theorem extCall_unreadable_conf_is_error (ffi : σ) :
    PancakeSem ⟨fun st _ _ _ => .ret st []⟩
        (.extCall "name" (.const 0) (.const 1) (.const 8) (.const 0))
        { bareState ffi with memaddrs := fun a => a == 8 }
      = (some .error, { bareState ffi with memaddrs := fun a => a == 8 }) := by
  simp [PancakeSem, eval, bareState, readByteArray, memLoadByte, byteAlign]

/-- **The external call itself rejects a reply of the wrong length.** The clause, not
just `callFFI`: an oracle that answers with more bytes than the array ends the run,
and no byte is written. -/
theorem extCall_overlong_reply_is_final (ffi : σ) :
    PancakeSem ⟨fun st _ _ _ => .ret st [0xEE, 0xEE]⟩
        (.extCall "name" (.const 0) (.const 0) (.const 8) (.const 1)) (bareState ffi)
      = (some (.finalFFI ⟨"name", [], [0], .failed⟩), emptyLocals (bareState ffi)) := by
  simp [PancakeSem, eval, bareState, readByteArray, memLoadByte, callFFI, emptyLocals,
        getByte, byteIndex]

/-- …and a reply of the declared length is written at the array. -/
theorem extCall_exact_reply_is_written (ffi : σ) :
    ∃ s', PancakeSem ⟨fun st _ _ _ => .ret st [0xEE]⟩
        (.extCall "name" (.const 0) (.const 0) (.const 8) (.const 1)) (bareState ffi) = (none, s')
      ∧ memLoadByte s'.memory (bareState ffi).memaddrs (bareState ffi).be 8 = some 0xEE := by
  have hrun : PancakeSem ⟨fun st _ _ _ => .ret st [0xEE]⟩
      (.extCall "name" (.const 0) (.const 0) (.const 8) (.const 1)) (bareState ffi)
      = (none, { bareState ffi with
                 memory := writeByteArray (bareState ffi).memaddrs (bareState ffi).be 8 [0xEE]
                   (bareState ffi).memory }) := by
    simp [PancakeSem, eval, bareState, readByteArray, memLoadByte, callFFI,
          getByte, byteIndex]
  refine ⟨_, hrun, ?_⟩
  simp [bareState, writeByteArray, memStoreByte, memLoadByte, byteAlign, byteIndex,
        getByte, setByte, wordSliceAlt]

/-- A byte store out of range keeps the memory the whole call was given: the
bytes already written by the tail go with it. -/
theorem writeByteArray_failed_head_keeps_memory :
    writeByteArray (fun w => w == 8) false 7 [0xAA, 0xBB] (fun _ => 0) 8 = 0 := by
  decide

/-- An oracle reply of the wrong length ends the run instead of being written. -/
theorem overlong_ffi_result_is_final (ffi : σ) :
    callFFI ⟨fun st _ _ _ => .ret st [0xEE, 0xEE]⟩ ffi "name" [] [0]
      = .final ⟨"name", [], [0], .failed⟩ := rfl

/-- …and so does a reply that is too short. -/
theorem short_ffi_result_is_final (ffi : σ) :
    callFFI ⟨fun st _ _ _ => .ret st []⟩ ffi "name" [] [0, 1]
      = .final ⟨"name", [], [0, 1], .failed⟩ := rfl

/-- A reply of the declared length is what gets written back. -/
theorem exact_ffi_result_is_written (ffi : σ) :
    callFFI ⟨fun st _ _ _ => .ret st [0xEE]⟩ ffi "name" [] [0] = .ret ffi [0xEE] := rfl

/-- The empty name never reaches the oracle, and the array is returned unchanged. -/
theorem empty_ffi_name_is_identity (ffi : σ) (oracle : Oracle σ) :
    callFFI oracle ffi "" [] [0, 1] = .ret ffi [0, 1] := rfl

end DN.Compiler
