-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionText

/-!
# DN.Server.SessionDate

`dateText`, if it returns, writes DATE's digits of the seconds in the wall word into a connection's output, and the
place past them in the session's return word (`dateText_run`), when `artDiv` divides as its contract says; the
digits are `SessionSpec.dateDigits` of the wall clock whose seconds they are (`dateBytes_wall`). `artCivilOf` gives
the day of the calendar (`artCivilOf_run`). So the session's code keeps `dateText`'s contract when it keeps
`artDiv`'s (`civilOk_of`, `dateOk_of`), and `connText` writes the text of every reply it has a branch for, whatever
its argument (`connText_reply`). A division by subtraction keeps `artDiv`'s contract (`divW_run`); one state meets
all of DATE's premises (`time_witness`).
-/

namespace DN.Server.SessionDate

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Bytes DN.Compiler.Preservation DN.Compiler.Frag DN.Server
  DN.News DN.News.DecimalRun DN.Server.SessionAppend DN.Server.SessionText

variable {σ : Type}

open SessionLayout
open DN.Server.Session (ownW)

/-! ### `dateText` -/

/-- `artDiv` as the code holds it: at the base `b`, the heap covering the layout with the powers of two in place,
from `x` and `d` in range, if it returns, it gives back `x / d`, changing no word. -/
def DivOk (o : Oracle σ) (b : Word) (code : String → Option (List String × PancakeProg)) : Prop :=
  ∃ body, code "artDiv" = some (["x", "d"], body) ∧ ∀ x d (s1 : PancakeState σ),
    s1.locals "x" = some (BitVec.ofNat 64 x) → s1.locals "d" = some (BitVec.ofNat 64 d) → s1.baseAddr = b →
    PowIn b s1.memory → Analyzer.Covers SessionLayout.size s1.memaddrs b → s1.code = code → x < 2 ^ 62 → 1 ≤ d →
    d ≤ 2 ^ 62 →
    SafeR o (fun s => s = s1) body (fun v m => v = BitVec.ofNat 64 (x / d) ∧ m = s1.memory) (fun _ => False)

/-- A day of the Gregorian calendar as `artCivilOf` gives it back: its year, month and day in one word. -/
def civilWord (z : Nat) : Nat :=
  (News.ArticleSpec.civilFromDays z).1 * 512 + (News.ArticleSpec.civilFromDays z).2.1 * 32 +
    (News.ArticleSpec.civilFromDays z).2.2

/-- `artCivilOf` as the code holds it: of a day since 1970, if it returns, it gives back `civilWord`, changing no
word. -/
def CivilOk (o : Oracle σ) (b : Word) (code : String → Option (List String × PancakeProg)) : Prop :=
  ∃ body, code "artCivilOf" = some (["days"], body) ∧ ∀ z (s1 : PancakeState σ),
    s1.locals "days" = some (BitVec.ofNat 64 z) → s1.baseAddr = b → PowIn b s1.memory →
    Analyzer.Covers SessionLayout.size s1.memaddrs b → s1.code = code → z < 2 ^ 30 →
    SafeR o (fun s => s = s1) body (fun v m => v = BitVec.ofNat 64 (civilWord z) ∧ m = s1.memory) (fun _ => False)

/-- `dateText`'s locals and words from its entry `s1`: connection `c`'s output at `ob`, every word but the
output's as at entry. -/
structure DCtx (b : Word) (c : Nat) (s1 s : PancakeState σ) : Prop where
  hob : s.locals "ob" = some (outAt b c)
  base : s.baseAddr = b
  memaddrs : s.memaddrs = s1.memaddrs
  be : s.be = s1.be
  code : s.code = s1.code
  words : ∀ w, ¬ OutWord b c w → s.memory w = s1.memory w

/-- The octets `W` written from `ofs` of connection `c`'s output, every other octet as at entry `s1`. -/
def DBytes (b : Word) (c ofs : Nat) (W : List (BitVec 8)) (s1 s : PancakeState σ) : Prop :=
  memBytesAt s.memory s.memaddrs s.be (outAt b c + BitVec.ofNat 64 ofs) W ∧
    ∀ a, (∀ i, i < W.length → a ≠ outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 i) →
      memLoadByte s.memory s.memaddrs s.be a = memLoadByte s1.memory s1.memaddrs s1.be a

/-- Locals holding the values given. -/
def LocalsAre (xs : List (String × Value)) (s : PancakeState σ) : Prop := ∀ p ∈ xs, s.locals p.1 = some p.2

theorem localsAre_set {xs : List (String × Value)} {s : PancakeState σ} (h : LocalsAre xs s) {y : String}
    (hy : y ∉ xs.map Prod.fst) (v : Value) : LocalsAre xs { s with locals := setLocal s.locals y v } :=
  fun p hp => by
    have : p.1 ≠ y := fun e => hy (e ▸ List.mem_map_of_mem hp)
    simp only [setLocal]
    rw [if_neg this]
    exact h p hp

/-- **A byte put after `W`** in `dateText`'s output. -/
theorem dput {b : Word} {c ofs : Nat} {s1 s : PancakeState σ} {W : List (BitVec 8)}
    (hc : c < conns) (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) (hroom : ofs + W.length < data)
    (hx : DCtx b c s1 s) (hw : DBytes b c ofs W s1 s) (y : BitVec 8) :
    s.memaddrs (byteAlign (outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 W.length)) = true ∧
    DCtx b c s1
    { s with memory := putByte s.memory s.be (outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 W.length) y } ∧
    DBytes b c ofs (W ++ [y]) s1
      { s with memory := putByte s.memory s.be (outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 W.length) y } := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  have hA : s.memaddrs (byteAlign (outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 W.length)) = true := by
    rw [hx.memaddrs, outAt_off, add_ofNat, add_ofNat]
    have := out_in hc hroom
    exact hcov.1 _ (by simp only [Analyzer.floor]; omega) (by omega)
  have hW : OutWord b c (byteAlign (outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 W.length)) :=
    ⟨ofs + W.length, hroom, by rw [add_ofNat]⟩
  refine ⟨hA, ⟨hx.hob, hx.base, hx.memaddrs, hx.be, hx.code, fun w hw' => ?_⟩, ?_, fun a ha => ?_⟩
  · simp only [putByte]
    rw [if_neg (fun (e : w = _) => hw' (e ▸ hW))]
    exact hx.words w hw'
  · exact memBytesAt_snoc hw.1 hA (by omega)
  · simp only
    rw [load_putByte_diff _ _ _ _ _ _ (ha W.length (by simp))]
    exact hw.2 a fun i hi => ha i (by simp; omega)

/-- `dateText`'s two digits of `x`, as it has them. -/
def twoS (x : Syntax.PExpr) : List Syntax.PStmt :=
  [SessionStore.keptIn (Syntax.v "o") (data - 2),
   .storeb (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) (Syntax.eAdd (Syntax.n 48) (SessionStore.div10 x)),
   .storeb (Syntax.eAdd (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) (Syntax.n 1))
     (Syntax.eAdd (Syntax.n 48) (Syntax.eSub x (Syntax.eMul (SessionStore.div10 x) (Syntax.n 10)))),
   .assign "o" (Syntax.eAdd (Syntax.v "o") (Syntax.n 2))]

/-- A number below a hundred in two digits. -/
def twoDigits (v : Nat) : List (BitVec 8) := [BitVec.ofNat 8 (48 + v / 10), BitVec.ofNat 8 (48 + v % 10)]

/-- `dateText`'s state from its entry `s1`: the context, the octets `W` written from `ofs` with `o` past them,
the locals `xs` holding their values. -/
def DState (b : Word) (c ofs : Nat) (W : List (BitVec 8)) (xs : List (String × Value)) (s1 s : PancakeState σ) : Prop :=
  DCtx b c s1 s ∧ s.locals "o" = some (BitVec.ofNat 64 (ofs + W.length)) ∧ DBytes b c ofs W s1 s ∧ LocalsAre xs s

theorem dstate_clock {b : Word} {c ofs : Nat} {W : List (BitVec 8)} {xs : List (String × Value)}
    {s1 : PancakeState σ} : Safe.ClockFree (DState b c ofs W xs s1) :=
  fun _ _ ⟨h, ho, hw, hl⟩ => ⟨{ h with }, ho, hw, hl⟩

/-- **Two digits of a number below a hundred** after those written. -/
theorem two_frag (o : Oracle σ) {b : Word} {c ofs : Nat} {s1 : PancakeState σ}
    {W : List (BitVec 8)} {xs : List (String × Value)} (hc : c < conns)
    (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) {x : Syntax.PExpr} {X : PancakeExp}
    (hx : Lower.lowerExp x = some X) {v : Nat} (hv : v < 100)
    (hX : ∀ s : PancakeState σ, LocalsAre xs s → s.baseAddr = b → eval s X = some (BitVec.ofNat 64 v))
    (hxs : "o" ∉ xs.map Prod.fst) (hroom : ofs + W.length + 2 ≤ data) :
    Frag o (twoS x) (DState b c ofs W xs s1) (DState b c ofs (W ++ twoDigits v) xs s1) := by
  have hd : data = 512 := nums.dataLen
  have hv32 : v < 2 ^ 32 := by omega
  have hdiv : Lower.lowerExp (SessionStore.div10 x) = some (div10E X) := by
    simp [SessionStore.div10, Lower.lowerExp, Syntax.eMul, Syntax.n, hx, div10E]
  let y1 : BitVec 8 := BitVec.ofNat 8 (48 + v / 10)
  let y2 : BitVec 8 := BitVec.ofNat 8 (48 + v % 10)
  have hk : Frag o [SessionStore.keptIn (Syntax.v "o") (data - 2)] (DState b c ofs W xs s1) (DState b c ofs W xs s1) :=
    frag_keptIn o (e := Syntax.v "o") rfl (by rw [hd]; decide) dstate_clock fun s h => ⟨_, by omega, h.2.1⟩
  let M1 : Assn σ := fun s => DCtx b c s1 s ∧ s.locals "o" = some (BitVec.ofNat 64 (ofs + W.length)) ∧
    DBytes b c ofs (W ++ [y1]) s1 s ∧ LocalsAre xs s
  let M2 : Assn σ := fun s => DCtx b c s1 s ∧ s.locals "o" = some (BitVec.ofNat 64 (ofs + W.length)) ∧
    DBytes b c ofs (W ++ [y1] ++ [y2]) s1 s ∧ LocalsAre xs s
  have cM1 : Safe.ClockFree M1 := fun _ _ ⟨h, ho, hw, hl⟩ => ⟨{ h with }, ho, hw, hl⟩
  have cM2 : Safe.ClockFree M2 := fun _ _ ⟨h, ho, hw, hl⟩ => ⟨{ h with }, ho, hw, hl⟩
  have s1f : Frag o [.storeb (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) (Syntax.eAdd (Syntax.n 48) (SessionStore.div10 x))]
      (DState b c ofs W xs s1) M1 := by
    refine frag_one (a := .storeByte (.op .add (.var "ob") (.var "o")) (.op .add (.const 48) (div10E X)))
      (by simp [Lower.lowerStmt1, Lower.lowerExp, Syntax.eAdd, Syntax.n, Syntax.v, hdiv]) rfl rfl cM1
      (Safe.storeByte fun s ⟨h, ho, hw, hl⟩ => ?_)
    obtain ⟨hA, h', hw'⟩ := dput hc hcov (by omega) h hw y1
    refine ⟨outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 W.length, BitVec.ofNat 64 (48 + v / 10),
      putByte s.memory s.be (outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 W.length) y1,
      by simp [eval, h.hob, ho, add_ofNat], by simp [eval, div10E_eval hv32 (hX s hl h.base), BitVec.ofNat_add],
      by rw [setWidth_ofNat_8]; exact memStore_eq _ _ _ _ _ hA, h', ho, hw', hl⟩
  have s2f : Frag o [.storeb (Syntax.eAdd (Syntax.eAdd (Syntax.v "ob") (Syntax.v "o")) (Syntax.n 1))
      (Syntax.eAdd (Syntax.n 48) (Syntax.eSub x (Syntax.eMul (SessionStore.div10 x) (Syntax.n 10))))] M1 M2 := by
    refine frag_one (a := .storeByte (.op .add (.op .add (.var "ob") (.var "o")) (.const (BitVec.ofNat 64 1)))
        (.op .add (.const 48) (.op .sub X (.mul (div10E X) (.const 10)))))
      (by simp [Lower.lowerStmt1, Lower.lowerExp, Syntax.eAdd, Syntax.eSub, Syntax.eMul, Syntax.n, Syntax.v, hx, hdiv])
      rfl rfl cM2 (Safe.storeByte fun s ⟨h, ho, hw, hl⟩ => ?_)
    have hl1 : (W ++ [y1]).length = W.length + 1 := by simp
    obtain ⟨hA, h', hw'⟩ := dput hc hcov (by rw [hl1]; omega) h hw y2
    rw [hl1] at hA h' hw'
    refine ⟨outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 (W.length + 1), BitVec.ofNat 64 (48 + v % 10),
      putByte s.memory s.be (outAt b c + BitVec.ofNat 64 ofs + BitVec.ofNat 64 (W.length + 1)) y2,
      by simp only [eval, h.hob, ho, add_ofNat, Nat.add_assoc], ?_,
      by rw [setWidth_ofNat_8]; exact memStore_eq _ _ _ _ _ hA,
      h', ho, by simpa using hw', hl⟩
    have hX' := hX s hl h.base
    simp only [eval, hX', div10E_eval hv32 hX']
    rw [digit_word v hv32]
  have af : Frag o [.assign "o" (Syntax.eAdd (Syntax.v "o") (Syntax.n 2))] M2
      (DState b c ofs (W ++ twoDigits v) xs s1) :=
    frag_one rfl rfl rfl dstate_clock (Safe.assign fun s ⟨h, ho, hw, hl⟩ => ⟨BitVec.ofNat 64 (ofs + W.length + 2), _,
      by simp [eval, ho, BitVec.ofNat_add], ho, ⟨⟨by simp [setLocal, h.hob], h.base, h.memaddrs, h.be, h.code, h.words⟩,
        by simp [setLocal, twoDigits, Nat.add_assoc], by simpa [twoDigits, y1, y2] using hw, localsAre_set hl hxs _⟩⟩)
  exact frag_append hk (frag_append s1f (frag_append s2f af))

/-- **A call to a function changing no word** that gives back `val`. -/
theorem pure_call (o : Oracle σ) {b : Word} {c ofs : Nat} {s1 : PancakeState σ} {W : List (BitVec 8)}
    {xs : List (String × Value)} {rt f : String} {as : List Syntax.PExpr} {args : List PancakeExp}
    (has : Lower.lowerArgs as = some args) {ps : List String} (hnd : ps.Nodup) {body : PancakeProg}
    (hcode : s1.code f = some (ps, body)) {vs : List Value} (hlen : ps.length = vs.length)
    (hargs : ∀ s, DState b c ofs W xs s1 s → evalArgs s args = some vs) {val : Value}
    (hsafe : ∀ s,
        DState b c ofs W xs s1 s → SafeR o (fun u => u = { decClock s with locals := fun k => (ps.zip vs).lookup k })
      body (fun v m => v = val ∧ m = s.memory) (fun _ => False))
    (hrt : rt ∉ xs.map Prod.fst) (hro : rt ≠ "o") (hrob : rt ≠ "ob") :
    Frag o [.call rt f as] (DState b c ofs W xs s1) (DState b c ofs W ((rt, val) :: xs) s1) :=
  frag_call o has (body := body)
    (Pc := fun s s2 => s2 = { decClock s with locals := fun k => (ps.zip vs).lookup k })
    (Rc := fun s v m => v = val ∧ m = s.memory) (fun s h => hsafe s h)
    (fun s h => ⟨vs, _, hargs s h, Block.lookupCode_of (by rw [h.1.code]; exact hcode) hnd hlen, rfl⟩)
    fun s u v ⟨h, ho, hw, hl⟩ ⟨hv, hm⟩ hsame => by
      subst hv
      refine ⟨⟨by simp [setLocal, Ne.symm hrob, h.hob], hsame.2.1.trans h.base, hsame.1.trans h.memaddrs,
        hsame.2.2.1.trans h.be, hsame.2.2.2.trans h.code, fun w hw' => (congrFun hm w).trans (h.words w hw')⟩,
        by simp [setLocal, Ne.symm hro, ho], ?_, fun p hp => ?_⟩
      · show DBytes b c ofs W s1 { u with locals := _ }
        simp only [DBytes]
        rw [hm, hsame.1, hsame.2.2.1]
        exact hw
      · rcases List.mem_cons.mp hp with rfl | hp
        · simp [setLocal]
        · exact localsAre_set hl hrt _ p hp

/-! ### The date's arithmetic -/

/-- A day of the calendar from a day since 1970 below 2^30: a year past 1600 and below 2^22, a month and a day
of the month in range. -/
theorem civil_range (z : Nat) (hz : z < 2 ^ 30) :
    1600 ≤ (News.ArticleSpec.civilFromDays z).1 ∧ (News.ArticleSpec.civilFromDays z).1 < 2 ^ 22 ∧
      1 ≤ (News.ArticleSpec.civilFromDays z).2.1 ∧ (News.ArticleSpec.civilFromDays z).2.1 ≤ 12 ∧
      1 ≤ (News.ArticleSpec.civilFromDays z).2.2 ∧ (News.ArticleSpec.civilFromDays z).2.2 ≤ 31 := by
  simp only [News.ArticleSpec.civilFromDays]
  split <;> split <;> omega

theorem and_mask (x k : Nat) (hx : x < 2 ^ 64) (hk : k < 64) :
    BitVec.ofNat 64 x &&& BitVec.ofNat 64 (2 ^ k - 1) = BitVec.ofNat 64 (x % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ k - 1 < 2 ^ 64 := by have := Nat.pow_lt_pow_right (a := 2) (by decide) hk; omega
  have h2 : x % 2 ^ k < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.and_two_pow_sub_one_eq_mod]

theorem shift_word (x k : Nat) (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> k = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

/-- A number below a hundred in two digits is its two places. -/
theorem padded_two {v : Nat} (hv : v < 100) : News.SessionSpec.padded 2 v = twoDigits v := by
  simp only [News.SessionSpec.padded, twoDigits]
  rw [decimal_eq]
  by_cases h : v < 10
  · simp [h, Decimal.digitByte, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
  · rw [if_neg h, decimal_eq, if_pos (by omega : v / 10 < 10)]
    simp [Decimal.digitByte]

/-- A year past 999 in four digits or more is its digits. -/
theorem padded_four {y : Nat} (hy : 1000 ≤ y) : News.SessionSpec.padded 4 y = CommandSpec.decimal y := by
  simp only [News.SessionSpec.padded, decimal_length]
  have := lt_pow_numDigits y
  have h4 : 4 ≤ numDigits y := by
    by_cases h : numDigits y ≤ 3
    · have : 10 ^ numDigits y ≤ 10 ^ 3 := Nat.pow_le_pow_right (by decide) h
      omega
    · omega
  rw [show 4 - numDigits y = 0 by omega]
  rfl

theorem dateBytes_eq (secs : Nat) (hs : secs < 2 ^ 40) :
    dateBytes secs = CommandSpec.decimal (News.ArticleSpec.civilFromDays (secs / 86400)).1 ++
      twoDigits (News.ArticleSpec.civilFromDays (secs / 86400)).2.1 ++
      twoDigits (News.ArticleSpec.civilFromDays (secs / 86400)).2.2 ++ twoDigits (secs % 86400 / 3600) ++
      twoDigits (secs % 86400 % 3600 / 60) ++ twoDigits (secs % 86400 % 60) := by
  obtain ⟨h1, -, -, h3, -, h5⟩ := civil_range (secs / 86400) (by omega)
  simp only [dateBytes, News.SessionSpec.dateDigits, Nat.mul_div_cancel _ (by decide : 0 < 1000)]
  rw [padded_four (by omega), padded_two (by omega), padded_two (by omega), padded_two (by omega),
    padded_two (by omega), padded_two (by omega)]

/-- A declaration in `dateText`, its value known. -/
theorem dval_frag (o : Oracle σ) {b : Word} {c ofs : Nat} {s1 : PancakeState σ} {W : List (BitVec 8)}
    {xs : List (String × Value)} {x : String} {e : Syntax.PExpr} {E : PancakeExp} (he : Lower.lowerExp e = some E)
    {v : Value} (hv : ∀ s, DState b c ofs W xs s1 s → eval s E = some v) (hx : x ∉ xs.map Prod.fst)
    (hxo : x ≠ "o") (hxob : x ≠ "ob") :
    Frag o [.dec x e] (DState b c ofs W xs s1) (DState b c ofs W ((x, v) :: xs) s1) :=
  frag_dec o he fun s h => ⟨v, hv s h, ⟨by simp [setLocal, Ne.symm hxob, h.1.hob], h.1.base, h.1.memaddrs, h.1.be,
    h.1.code, h.1.words⟩, by simp [setLocal, Ne.symm hxo, h.2.1], h.2.2.1, fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [setLocal]
      · exact localsAre_set h.2.2.2 hx _ p hp⟩

/-- The statements before `dateText`'s digits. -/
def dateHead : List Syntax.PStmt := Session.dateText.body.take 13

theorem date_split : Session.dateText.body = dateHead ++
    (SessionStore.digits "yd" (Syntax.v "ob") "o" (Syntax.v "yr") data ++
    (twoS (Syntax.v "mo") ++ (twoS (Syntax.v "dy") ++ (twoS (Syntax.v "hr") ++ (twoS (Syntax.v "mn") ++
    (twoS (Syntax.eSub (Syntax.v "rest") (Syntax.eMul (Syntax.v "mn") (Syntax.n 60))) ++
    SessionStore.give (Syntax.v "o"))))))) := by
  rfl

theorem localsAre_get {xs : List (String × Value)} {s : PancakeState σ} (h : LocalsAre xs s) {x : String} {v : Value}
    (hp : (x, v) ∈ xs) : s.locals x = some v := h _ hp

theorem mod_word (x k : Nat) (hx : x < 2 ^ 40) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 (x / k) * BitVec.ofNat 64 k = BitVec.ofNat 64 (x % k) := by
  rw [← BitVec.ofNat_mul, SessionCheck.sub_small x (x / k * k) (Nat.div_mul_le_self x k) (by omega),
    show x - x / k * k = x % k by rw [Nat.mod_def, Nat.mul_comm]]

/-- **`dateText`'s first statements**: the output's place, the wall clock's seconds, and from them the day, the
time of the day and the calendar, each in its local. -/
theorem dateHead_frag (o : Oracle σ) {b : Word} {c ofs secs : Nat} {s1 : PancakeState σ}
    (he : DEntry b c ofs secs s1) (hofs : ofs ≤ 8) (hsecs : secs < 2 ^ 40)
    (hdiv : DivOk o b s1.code) (hciv : CivilOk o b s1.code) :
    Frag o dateHead (fun s => s = s1) (DState b c ofs [] [
      ("mn", BitVec.ofNat 64 (secs % 86400 % 3600 / 60)), ("rest", BitVec.ofNat 64 (secs % 86400 % 3600)),
      ("hr", BitVec.ofNat 64 (secs % 86400 / 3600)), ("yr",
          BitVec.ofNat 64 (News.ArticleSpec.civilFromDays (secs / 86400)).1),
      ("mo", BitVec.ofNat 64 (News.ArticleSpec.civilFromDays (secs / 86400)).2.1),
      ("dy", BitVec.ofNat 64 (News.ArticleSpec.civilFromDays (secs / 86400)).2.2),
      ("cv", BitVec.ofNat 64 (civilWord (secs / 86400))), ("sd", BitVec.ofNat 64 (secs % 86400)),
      ("dd", BitVec.ofNat 64 (secs / 86400)), ("sc", BitVec.ofNat 64 secs)] s1) := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  obtain ⟨dbody, hdcode, hdsafe⟩ := hdiv
  obtain ⟨cbody, hccode, hcsafe⟩ := hciv
  have hz : secs / 86400 < 2 ^ 30 := by omega
  obtain ⟨y1, y2, m1, m2, d1, d2⟩ := civil_range _ hz
  generalize hcf : News.ArticleSpec.civilFromDays (secs / 86400) = cf at y1 y2 m1 m2 d1 d2 ⊢
  obtain ⟨y, m, dd⟩ := cf
  simp only at y1 y2 m1 m2 d1 d2 ⊢
  have hcw : civilWord (secs / 86400) = y * 512 + m * 32 + dd := by simp [civilWord, hcf]
  have e : dateHead = [SessionStore.keptIn (Syntax.v "c") (conns - 1), SessionStore.keptIn (Syntax.v "o") 8,
      .dec "ob" (Syntax.atOff (Session.record (Syntax.v "c")) cOut), .dec "sc" (ownW ownWall),
      .call "dd" "artDiv" [Syntax.v "sc", Syntax.n 86400],
      .dec "sd" (Syntax.eSub (Syntax.v "sc") (Syntax.eMul (Syntax.v "dd") (Syntax.n 86400))),
      .call "cv" "artCivilOf" [Syntax.v "dd"], .dec "dy" (Syntax.eAnd (Syntax.v "cv") (Syntax.n 31)),
      .dec "mo" (Syntax.eAnd (.shr (Syntax.v "cv") (Syntax.n 5)) (Syntax.n 15)), .dec "yr" (.shr (Syntax.v "cv") (Syntax.n 9)),
      .call "hr" "artDiv" [Syntax.v "sd", Syntax.n 3600],
      .dec "rest" (Syntax.eSub (Syntax.v "sd") (Syntax.eMul (Syntax.v "hr") (Syntax.n 3600))),
      .call "mn" "artDiv" [Syntax.v "rest", Syntax.n 60]] := rfl
  rw [e]
  -- the entry, the output's place
  let P0 : Assn σ := fun s => DEntry b c ofs secs s ∧ s.memory = s1.memory ∧ s.memaddrs = s1.memaddrs ∧
    s.be = s1.be ∧ s.code = s1.code
  have cP0 : Safe.ClockFree P0 := fun _ _ ⟨h, rest⟩ => ⟨{ h with }, rest⟩
  have k1 : Frag o [SessionStore.keptIn (Syntax.v "c") (conns - 1)] P0 P0 :=
    frag_keptIn o (e := Syntax.v "c") rfl (by decide) cP0 fun s h => ⟨c, by have := h.1.hcc; omega, h.1.hc⟩
  have k2 : Frag o [SessionStore.keptIn (Syntax.v "o") 8] P0 P0 :=
    frag_keptIn o (e := Syntax.v "o") rfl (by decide) cP0 fun s h => ⟨ofs, hofs, h.1.ho⟩
  obtain ⟨E, hE⟩ := record_lower
  have dob : Frag o [.dec "ob" (Syntax.atOff (Session.record (Syntax.v "c")) cOut)] P0 (DState b c ofs [] [] s1) :=
    frag_dec o (E := .op .add E (.const (BitVec.ofNat 64 cOut)))
      (atOff_lower hE (by rw [nums.out]; decide)) fun s h => ⟨outAt b c,
        by simp [eval, record_eval h.1.base h.1.hc hE, outAt],
        ⟨by simp [setLocal], h.1.base, h.2.2.1, h.2.2.2.1, h.2.2.2.2, fun w _ => by simp [h.2.1]⟩,
        by simp [setLocal, h.1.ho], ⟨fun i hi => by simp at hi, fun a _ => by simp [h.2.1, h.2.2.1, h.2.2.2.1]⟩,
        fun p hp => by simp at hp⟩
  -- the seconds
  have hwX : (ownOff + ownWall) % 8 = 0 ∧ 64 ≤ ownOff + ownWall ∧ ownOff + ownWall < tOff := by
    have : ownOff % 8 = 0 ∧ ownWall % 8 = 0 ∧ ownWall < ownTexts := by decide
    rw [hT]; omega
  have dsc := dval_frag o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := []) (x := "sc")
    (ownW_lower ownWall) (v := BitVec.ofNat 64 secs) (fun s h => by
      have hA := own_addr he.hcov hwX.1 hwX.2.1 hwX.2.2
      have hw : ¬ OutWord b c (b + BitVec.ofNat 64 (ownOff + ownWall)) := by
        rw [← byteAlign_of_aligned he.hb hwX.1]
        exact below_table he.hb he.hcc hwX.2.2
      simp only [eval, h.1.base, h.1.memaddrs, hA, if_true, h.1.words _ hw, he.hwall]) (by simp) (by decide) (by decide)
  -- the day and the time of the day
  have cdd := pure_call o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := [("sc", BitVec.ofNat 64 secs)])
    (rt := "dd") (f := "artDiv") (as := [Syntax.v "sc", Syntax.n 86400]) rfl (ps := ["x", "d"]) (by decide) hdcode
    (vs := [BitVec.ofNat 64 secs, BitVec.ofNat 64 86400]) rfl
    (fun s h => by simp [evalArgs, eval, localsAre_get h.2.2.2 (List.mem_singleton_self _)])
    (val := BitVec.ofNat 64 (secs / 86400))
    (fun s h => hdsafe secs 86400 _ (by simp) rfl h.1.base
      (pow_keep he.hb he.hcc (fun w hw _ => h.1.words w hw) he.hpow) (h.1.memaddrs ▸ he.hcov) h.1.code (by omega)
      (by decide) (by decide)) (by simp) (by decide) (by decide)
  let X2 := [("dd", BitVec.ofNat 64 (secs / 86400)), ("sc", BitVec.ofNat 64 secs)]
  have dsd := dval_frag o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := X2) (x := "sd")
    (e := Syntax.eSub (Syntax.v "sc") (Syntax.eMul (Syntax.v "dd") (Syntax.n 86400))) rfl
    (v := BitVec.ofNat 64 (secs % 86400)) (fun s h => by
      simp only [eval, localsAre_get h.2.2.2 (show ("sc", BitVec.ofNat 64 secs) ∈ X2 by simp [X2]),
        localsAre_get h.2.2.2 (show ("dd", BitVec.ofNat 64 (secs / 86400)) ∈ X2 by simp [X2])]
      rw [mod_word secs 86400 hsecs]) (by simp [X2]) (by decide) (by decide)
  let X3 := ("sd", BitVec.ofNat 64 (secs % 86400)) :: X2
  have ccv := pure_call o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := X3)
    (rt := "cv") (f := "artCivilOf") (as := [Syntax.v "dd"]) rfl (ps := ["days"]) (by decide) hccode
    (vs := [BitVec.ofNat 64 (secs / 86400)]) rfl
    (fun s h => by simp [evalArgs, eval, localsAre_get h.2.2.2 (show ("dd", BitVec.ofNat 64 (secs / 86400)) ∈ X3 by simp [X3,
        X2])])
    (val := BitVec.ofNat 64 (civilWord (secs / 86400)))
    (fun s h => hcsafe (secs / 86400) _ (by simp) h.1.base (pow_keep he.hb he.hcc (fun w hw _ => h.1.words w hw) he.hpow)
      (h.1.memaddrs ▸ he.hcov) h.1.code hz) (by simp [X3, X2]) (by decide) (by decide)
  -- the calendar
  have hcw64 : civilWord (secs / 86400) < 2 ^ 64 := by rw [hcw]; omega
  let X4 := ("cv", BitVec.ofNat 64 (civilWord (secs / 86400))) :: X3
  have hcv : ∀ s, DState b c ofs [] X4 s1 s → s.locals "cv" = some (BitVec.ofNat 64 (civilWord (secs / 86400))) :=
    fun s h => localsAre_get h.2.2.2 (by simp [X4])
  have ddy := dval_frag o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := X4) (x := "dy")
    (e := Syntax.eAnd (Syntax.v "cv") (Syntax.n 31)) rfl (v := BitVec.ofNat 64 dd) (fun s h => by
      simp only [eval, hcv s h]
      rw [show (BitVec.ofNat 64 31 : Word) = BitVec.ofNat 64 (2 ^ 5 - 1) from rfl, and_mask _ 5 hcw64 (by decide), hcw,
        show (y * 512 + m * 32 + dd) % 2 ^ 5 = dd by omega]) (by simp [X4, X3, X2]) (by decide) (by decide)
  let X5 := ("dy", BitVec.ofNat 64 dd) :: X4
  have dmo := dval_frag o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := X5) (x := "mo")
    (e := Syntax.eAnd (.shr (Syntax.v "cv") (Syntax.n 5)) (Syntax.n 15)) rfl (v := BitVec.ofNat 64 m) (fun s h => by
      simp only [eval, localsAre_get h.2.2.2 (show ("cv", BitVec.ofNat 64 (civilWord (secs / 86400))) ∈ X5 by simp [X5, X4])]
      rw [show (BitVec.ofNat 64 5 : Word).toNat = 5 from rfl]
      simp only [show (5 ≠ 0 && 5 ≥ 64) = false by decide, Bool.false_eq_true, if_false]
      rw [shift_word _ 5 hcw64, show (BitVec.ofNat 64 15 : Word) = BitVec.ofNat 64 (2 ^ 4 - 1) from rfl,
        and_mask _ 4 (by omega) (by decide), hcw, show (y * 512 + m * 32 + dd) / 2 ^ 5 % 2 ^ 4 = m by omega])
    (by simp [X5, X4, X3, X2]) (by decide) (by decide)
  let X6 := ("mo", BitVec.ofNat 64 m) :: X5
  have dyr := dval_frag o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := X6) (x := "yr")
    (e := .shr (Syntax.v "cv") (Syntax.n 9)) rfl (v := BitVec.ofNat 64 y) (fun s h => by
      simp only [eval, localsAre_get h.2.2.2 (show ("cv", BitVec.ofNat 64 (civilWord (secs / 86400))) ∈ X6 by simp [X6, X5, X4])]
      rw [show (BitVec.ofNat 64 9 : Word).toNat = 9 from rfl]
      simp only [show (9 ≠ 0 && 9 ≥ 64) = false by decide, Bool.false_eq_true, if_false]
      rw [shift_word _ 9 hcw64, hcw, show (y * 512 + m * 32 + dd) / 2 ^ 9 = y by omega])
    (by simp [X6, X5, X4, X3, X2]) (by decide) (by decide)
  -- the hour, the rest of the hour and the minute
  let X7 := ("yr", BitVec.ofNat 64 y) :: X6
  have chr := pure_call o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := X7)
    (rt := "hr") (f := "artDiv") (as := [Syntax.v "sd", Syntax.n 3600]) rfl (ps := ["x", "d"]) (by decide) hdcode
    (vs := [BitVec.ofNat 64 (secs % 86400), BitVec.ofNat 64 3600]) rfl
    (fun s h => by simp [evalArgs, eval, localsAre_get h.2.2.2 (show ("sd", BitVec.ofNat 64 (secs % 86400)) ∈ X7 by
      simp [X7, X6, X5, X4, X3])])
    (val := BitVec.ofNat 64 (secs % 86400 / 3600))
    (fun s h => hdsafe (secs % 86400) 3600 _ (by simp) rfl h.1.base
      (pow_keep he.hb he.hcc (fun w hw _ => h.1.words w hw) he.hpow) (h.1.memaddrs ▸ he.hcov) h.1.code
      (by omega) (by decide) (by decide)) (by simp [X7, X6, X5, X4, X3, X2]) (by decide) (by decide)
  let X8 := ("hr", BitVec.ofNat 64 (secs % 86400 / 3600)) :: X7
  have drest := dval_frag o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := X8) (x := "rest")
    (e := Syntax.eSub (Syntax.v "sd") (Syntax.eMul (Syntax.v "hr") (Syntax.n 3600))) rfl
    (v := BitVec.ofNat 64 (secs % 86400 % 3600)) (fun s h => by
      simp only [eval, localsAre_get h.2.2.2 (show ("sd", BitVec.ofNat 64 (secs % 86400)) ∈ X8 by simp [X8, X7, X6, X5, X4, X3]),
        localsAre_get h.2.2.2 (show ("hr", BitVec.ofNat 64 (secs % 86400 / 3600)) ∈ X8 by simp [X8])]
      rw [mod_word _ 3600 (by omega)]) (by simp [X8, X7, X6, X5, X4, X3, X2]) (by decide)
      (by decide)
  let X9 := ("rest", BitVec.ofNat 64 (secs % 86400 % 3600)) :: X8
  have cmn := pure_call o (s1 := s1) (b := b) (c := c) (ofs := ofs) (W := []) (xs := X9)
    (rt := "mn") (f := "artDiv") (as := [Syntax.v "rest", Syntax.n 60]) rfl (ps := ["x", "d"]) (by decide) hdcode
    (vs := [BitVec.ofNat 64 (secs % 86400 % 3600), BitVec.ofNat 64 60]) rfl
    (fun s h => by simp [evalArgs, eval, localsAre_get h.2.2.2 (show ("rest", BitVec.ofNat 64 (secs % 86400 % 3600)) ∈ X9 by
      simp [X9])])
    (val := BitVec.ofNat 64 (secs % 86400 % 3600 / 60))
    (fun s h => hdsafe (secs % 86400 % 3600) 60 _ (by simp) rfl h.1.base
      (pow_keep he.hb he.hcc (fun w hw _ => h.1.words w hw) he.hpow) (h.1.memaddrs ▸ he.hcov) h.1.code
      (by omega) (by decide) (by decide)) (by simp [X9, X8, X7, X6, X5, X4, X3, X2]) (by decide) (by decide)
  refine frag_conseq (frag_append k1 (frag_append k2 (frag_append dob (frag_append dsc (frag_append cdd
    (frag_append dsd (frag_append ccv (frag_append ddy (frag_append dmo (frag_append dyr (frag_append chr
    (frag_append drest cmn)))))))))))) (fun s hs => ?_) (fun s h => h)
  subst hs
  exact ⟨he, rfl, rfl, rfl, rfl⟩

/-- **The year's digits** in `dateText`'s output. -/
theorem ddigits_frag (o : Oracle σ) {b : Word} {c ofs : Nat} {s1 : PancakeState σ}
    {xs : List (String × Value)} (hc : c < conns) (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b)
    {x : String} {v : Nat} (hv : v < 2 ^ 32) (hx : (x, BitVec.ofNat 64 v) ∈ xs)
    (hxn : x ≠ "ydn" ∧ x ≠ "ydt" ∧ x ≠ "ydq")
    (hns : "ydn" ∉ xs.map Prod.fst ∧ "ydt" ∉ xs.map Prod.fst ∧ "ydq" ∉ xs.map Prod.fst ∧ "o" ∉ xs.map Prod.fst)
    (hroom : ofs + 10 ≤ data) :
    Frag o (SessionStore.digits "yd" (Syntax.v "ob") "o" (Syntax.v x) data) (DState b c ofs [] xs s1)
      (DState b c ofs (CommandSpec.decimal v) xs s1) := by
  have hN := numDigits_le_ten v hv
  have hl := decimal_length v
  have hd : data = 512 := nums.dataLen
  refine digits_frag o (DST := .var "ob") (X := .var x) rfl rfl fun s ⟨h, ho, hw, hla⟩ =>
    ⟨v, ofs, outAt b c, ⟨by decide, by decide, by decide, by decide, by decide, by decide, hv, by omega, by omega,
      by simpa using ho, localsAre_get hla hx, by simp only [ExpAvoids]; exact fun h' => by rcases h' with e | e | e <;>
        simp_all, by simp [eval, h.hob], trivial, by simp [ExpAvoids], fun i hi => ?_⟩, fun u hu => ?_⟩
  · rw [h.memaddrs, outAt_off, add_ofNat, add_ofNat]
    have := out_in hc (show ofs + i < data by omega)
    exact hcov.1 _ (by simp only [Analyzer.floor]; omega) this.2
  · have hloc : ∀ y, y ∉ ["ydn", "ydt", "ydq", "o"] → u.locals y = s.locals y := fun y hy => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hy
      exact hu.locals y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
    refine ⟨⟨by rw [hloc "ob" (by decide)]; exact h.hob, hu.base.trans h.base, hu.memaddrs.trans h.memaddrs,
      hu.be.trans h.be, hu.code.trans h.code, fun w hw' => ?_⟩, by rw [hu.hoff, hl], ⟨fun i hi => ?_, fun a ha => ?_⟩,
      fun p hp => ?_⟩
    · rw [hu.words w fun i hi e => hw' ⟨ofs + i, by omega, by rw [e, add_ofNat]⟩]
      exact h.words w hw'
    · rw [hu.digits i (by omega)]; simp [List.getElem?_eq_getElem hi]
    · rw [hu.bytes a fun i hi => ha i (by omega)]
      exact hw.2 a fun i hi => absurd hi (by simp)
    · have hp1 : p.1 ∉ ["ydn", "ydt", "ydq", "o"] := by
        intro hm
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
        have hpm := List.mem_map_of_mem (f := Prod.fst) hp
        rcases hm with e | e | e | e <;> rw [e] at hpm <;>
          first | exact hns.1 hpm | exact hns.2.1 hpm | exact hns.2.2.1 hpm | exact hns.2.2.2 hpm
      rw [hloc p.1 hp1]
      exact hla p hp

/-- **`dateText`**: from its entry at place `ofs` up to 8, if it returns, DATE's digits of the seconds in the wall
word written there, the place past them in the return word, zero returned; `artDiv` and `artCivilOf` as their
contracts say. -/
theorem dateText_run (o : Oracle σ) {b : Word} {c ofs secs : Nat} {s1 : PancakeState σ}
    (he : DEntry b c ofs secs s1) (hofs : ofs ≤ 8) (hsecs : secs < 2 ^ 40)
    (hdiv : DivOk o b s1.code) (hciv : CivilOk o b s1.code) :
    ∃ k, Lower.lowerStmtsFold Session.dateText.body = some k ∧
      SafeR o (fun s => s = s1) k (DateRet b c ofs (dateBytes secs) s1.memaddrs s1.be s1.memory)
        (fun _ => False) := by
  obtain ⟨T, hT, h8, hend, hown⟩ := lay
  obtain ⟨-, -, -, hd, hn, h64⟩ := nums
  have hz : secs / 86400 < 2 ^ 30 := by omega
  obtain ⟨y1, y2, m1, m2, d1, d2⟩ := civil_range _ hz
  have hF1 := dateHead_frag o he hofs hsecs hdiv hciv
  rw [dateBytes_eq secs hsecs]
  generalize hcf : News.ArticleSpec.civilFromDays (secs / 86400) = cf at y1 y2 m1 m2 d1 d2 hF1 ⊢
  obtain ⟨y, m, dd⟩ := cf
  simp only at y1 y2 m1 m2 d1 d2 hF1 ⊢
  have hcc := he.hcc
  rw [hn] at hcc
  let xs : List (String × Value) := [("mn", BitVec.ofNat 64 (secs % 86400 % 3600 / 60)),
    ("rest", BitVec.ofNat 64 (secs % 86400 % 3600)), ("hr", BitVec.ofNat 64 (secs % 86400 / 3600)),
    ("yr", BitVec.ofNat 64 y), ("mo", BitVec.ofNat 64 m), ("dy", BitVec.ofNat 64 dd),
    ("cv", BitVec.ofNat 64 (civilWord (secs / 86400))), ("sd", BitVec.ofNat 64 (secs % 86400)),
    ("dd", BitVec.ofNat 64 (secs / 86400)), ("sc", BitVec.ofNat 64 secs)]
  have hF2 := ddigits_frag o (s1 := s1) (ofs := ofs) (xs := xs) hcc he.hcov (x := "yr") (v := y) (by omega)
    (by simp [xs]) (by decide) (by simp [xs]) (by omega)
  have hN := numDigits_le_ten y (by omega)
  have hdl := decimal_length y
  have hv : ∀ (x : String) (v : Nat), (x, BitVec.ofNat 64 v) ∈ xs → ∀ s : PancakeState σ, LocalsAre xs s →
      s.baseAddr = b → eval s (.var x) = some (BitVec.ofNat 64 v) := fun x v hm s hl _ => localsAre_get hl hm
  have hT1 := two_frag o (s1 := s1) (ofs := ofs) (W := CommandSpec.decimal y) (xs := xs) hcc he.hcov
      (x := Syntax.v "mo")
    (X := .var "mo") rfl (v := m) (by omega) (hv "mo" m (by simp [xs])) (by simp [xs]) (by omega)
  have hT2 := two_frag o (s1 := s1) (ofs := ofs) (W := CommandSpec.decimal y ++ twoDigits m) (xs := xs) hcc he.hcov
    (x := Syntax.v "dy") (X := .var "dy") rfl (v := dd) (by omega) (hv "dy" dd (by simp [xs])) (by simp [xs])
    (by simp [twoDigits]; omega)
  have hT3 := two_frag o (s1 := s1) (ofs := ofs) (W := CommandSpec.decimal y ++ twoDigits m ++ twoDigits dd)
      (xs := xs) hcc he.hcov
    (x := Syntax.v "hr") (X := .var "hr") rfl (v := secs % 86400 / 3600) (by omega)
    (hv "hr" _ (by simp [xs])) (by simp [xs]) (by simp [twoDigits]; omega)
  have hT4 := two_frag o (s1 := s1) (ofs := ofs) (W := CommandSpec.decimal y ++ twoDigits m ++ twoDigits dd ++
      twoDigits (secs % 86400 / 3600)) (xs := xs) hcc he.hcov
    (x := Syntax.v "mn") (X := .var "mn") rfl (v := secs % 86400 % 3600 / 60) (by omega)
    (hv "mn" _ (by simp [xs])) (by simp [xs]) (by simp [twoDigits]; omega)
  have hT5 := two_frag o (s1 := s1) (ofs := ofs) (W := CommandSpec.decimal y ++ twoDigits m ++ twoDigits dd ++
      twoDigits (secs % 86400 / 3600) ++ twoDigits (secs % 86400 % 3600 / 60)) (xs := xs) hcc he.hcov
    (x := Syntax.eSub (Syntax.v "rest") (Syntax.eMul (Syntax.v "mn") (Syntax.n 60)))
    (X := .op .sub (.var "rest") (.mul (.var "mn") (.const (BitVec.ofNat 64 60)))) rfl
    (v := secs % 86400 % 60) (by omega) (fun s hl _ => by
      simp only [eval, localsAre_get hl (show ("rest", BitVec.ofNat 64 (secs % 86400 % 3600)) ∈ xs by simp [xs]),
        localsAre_get hl (show ("mn", BitVec.ofNat 64 (secs % 86400 % 3600 / 60)) ∈ xs by simp [xs])]
      rw [mod_word _ 60 (by omega), show secs % 86400 % 3600 % 60 = secs % 86400 % 60 by omega])
    (by simp [xs]) (by simp [twoDigits]; omega)
  -- the place past them in the return word, zero returned
  let Wf := CommandSpec.decimal y ++ twoDigits m ++ twoDigits dd ++ twoDigits (secs % 86400 / 3600) ++
    twoDigits (secs % 86400 % 3600 / 60) ++ twoDigits (secs % 86400 % 60)
  have hro := ret_in
  have hgive : Lower.lowerStmtsFold (SessionStore.give (Syntax.v "o")) =
      some (.seq (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet)))) (.var "o"))
        (.ret (.const (BitVec.ofNat 64 0)))) := by
    simp [SessionStore.give, Lower.lowerStmtsFold, Lower.lowerStmt1, Lower.lowerExp, at_lower hro.2.2.2, Syntax.v,
      Syntax.n]
  have hA := own_addr he.hcov hro.1 hro.2.1 hro.2.2.1
  rw [show b + BitVec.ofNat 64 (ownOff + ownRet) = SessionCheck.retW b from rfl] at hA
  have hR : SafeR o (DState b c ofs Wf xs s1) (.seq (.store (.op .add .base
      (.const (BitVec.ofNat 64 (ownOff + ownRet)))) (.var "o")) (.ret (.const (BitVec.ofNat 64 0))))
      (DateRet b c ofs Wf s1.memaddrs s1.be s1.memory) (fun _ => False) := by
    refine WpRet.seq (M := fun s => DateRet b c ofs Wf s1.memaddrs s1.be s1.memory 0 s.memory)
      (WpRet.store fun s ⟨h, ho, hw, _⟩ => ⟨SessionCheck.retW b, BitVec.ofNat 64 (ofs + Wf.length),
        fun k => if k = SessionCheck.retW b then BitVec.ofNat 64 (ofs + Wf.length) else s.memory k,
        by simp [eval, h.base, SessionCheck.retW], ho, by simp [memStoreWord, h.memaddrs, hA], ?_⟩)
      (WpRet.ret fun s h => ⟨0, rfl, h⟩) (fun _ _ h => h)
    have hnr : ∀ a, byteAlign a ≠ SessionCheck.retW b →
        memLoadByte (fun k => if k = SessionCheck.retW b then BitVec.ofNat 64 (ofs + Wf.length) else s.memory k)
          s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a := fun a ha =>
      load_of_word (by simp [ha])
    refine ⟨rfl, fun i hi => ?_, by simp, fun a ha hr => ?_, fun w hw' hr => ?_⟩
    · rw [← h.memaddrs, ← h.be, hnr _ (fun e => retW_out he.hb he.hcc
        (e ▸ ⟨ofs + i, by have := hdl; simp [Wf, twoDigits] at hi; omega, by rw [add_ofNat]⟩))]
      exact hw.1 i hi
    · have e1 := hnr a hr
      have e2 := hw.2 a ha
      rw [h.memaddrs, h.be] at e1 e2
      rw [e1, e2]
    · simp only [hr, if_false]
      exact h.words w hw'
  obtain ⟨k, hk, hks⟩ := frag_append hF1 (frag_append hF2 (frag_append hT1 (frag_append hT2 (frag_append hT3
    (frag_append hT4 hT5))))) _ _ _ (fun _ _ _ h _ => h) hR
  refine ⟨k, ?_, hks⟩
  rw [date_split]
  simp only [← List.append_assoc]
  rw [Block.fold_split _ _ (by simp [SessionStore.give]) hgive]
  simpa only [List.append_assoc] using hk

/-! ### `artCivilOf` -/

/-- A state of a function that changes no word, from its entry `s1`: the locals `xs` holding their values. -/
def CState (s1 : PancakeState σ) (xs : List (String × Value)) (s : PancakeState σ) : Prop :=
  s.memory = s1.memory ∧ s.memaddrs = s1.memaddrs ∧ s.be = s1.be ∧ s.baseAddr = s1.baseAddr ∧ s.code = s1.code ∧
    LocalsAre xs s

theorem cstate_clock {s1 : PancakeState σ} {xs : List (String × Value)} : Safe.ClockFree (CState s1 xs) :=
  fun _ _ h => h

theorem cval_frag (o : Oracle σ) {s1 : PancakeState σ} {xs : List (String × Value)} {x : String} {e : Syntax.PExpr}
    {E : PancakeExp} (he : Lower.lowerExp e = some E) {v : Value} (hv : ∀ s, CState s1 xs s → eval s E = some v)
    (hx : x ∉ xs.map Prod.fst) : Frag o [.dec x e] (CState s1 xs) (CState s1 ((x, v) :: xs)) :=
  frag_dec o he fun s h => ⟨v, hv s h, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [setLocal]
    · exact localsAre_set h.2.2.2.2.2 hx _ p hp⟩

theorem ccall_frag (o : Oracle σ) {s1 : PancakeState σ} {xs : List (String × Value)} {rt f : String}
    {as : List Syntax.PExpr} {args : List PancakeExp} (has : Lower.lowerArgs as = some args) {ps : List String}
    (hnd : ps.Nodup) {body : PancakeProg} (hcode : s1.code f = some (ps, body)) {vs : List Value}
    (hlen : ps.length = vs.length) (hargs : ∀ s, CState s1 xs s → evalArgs s args = some vs) {val : Value}
    (hsafe : ∀ s, CState s1 xs s → SafeR o (fun u => u = { decClock s with locals := fun k => (ps.zip vs).lookup k })
      body (fun v m => v = val ∧ m = s.memory) (fun _ => False))
    (hrt : rt ∉ xs.map Prod.fst) : Frag o [.call rt f as] (CState s1 xs) (CState s1 ((rt, val) :: xs)) :=
  frag_call o has (body := body)
    (Pc := fun s s2 => s2 = { decClock s with locals := fun k => (ps.zip vs).lookup k })
    (Rc := fun s v m => v = val ∧ m = s.memory) (fun s h => hsafe s h)
    (fun s h => ⟨vs, _, hargs s h, Block.lookupCode_of (by rw [h.2.2.2.2.1]; exact hcode) hnd hlen, rfl⟩)
    fun s u v h ⟨hv, hm⟩ hsame => by
      subst hv
      exact ⟨hm.trans h.1, hsame.1.trans h.2.1, hsame.2.2.1.trans h.2.2.1, hsame.2.1.trans h.2.2.2.1,
        hsame.2.2.2.trans h.2.2.2.2.1, fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp
          · simp [setLocal]
          · exact localsAre_set h.2.2.2.2.2 hrt _ p hp⟩

/-- The day of the year never falls below the year's start: no step of `artCivilOf` goes below zero. -/
theorem cal_doe (doe : Nat) (h : doe < 146097) :
    365 * ((doe - doe / 1460 + doe / 36524 - doe / 146096) / 365) +
      (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 / 4 -
      (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 / 100 ≤ doe := by
  generalize ha1 : doe / 1460 = a1
  generalize ha2 : doe / 36524 = a2
  generalize ha3 : doe / 146096 = a3
  have e1 : 1460 * a1 ≤ doe ∧ doe < 1460 * a1 + 1460 := by omega
  have e2 : 36524 * a2 ≤ doe ∧ doe < 36524 * a2 + 36524 := by omega
  have e3 : 146096 * a3 ≤ doe ∧ doe < 146096 * a3 + 146096 := by omega
  have h21 : a2 ≤ a1 := by omega
  generalize hy : (doe - a1 + a2 - a3) / 365 = y
  have ey : 365 * y ≤ doe - a1 + a2 - a3 ∧ doe - a1 + a2 - a3 < 365 * y + 365 := by omega
  have i1 : y / 4 ≤ a1 := by omega
  have i2 : a2 - a3 ≤ y / 100 := by
    rcases (show a2 = 0 ∨ a2 = 1 ∨ a2 = 2 ∨ a2 = 3 ∨ a2 = 4 by omega) with h2 | h2 | h2 | h2 | h2 <;>
      subst h2 <;> omega
  omega

/-- **`artCivilOf`**: of a day since 1970 below 2^30, if it returns, the day of the calendar in one word, changing
no word; `artDiv` as its contract says. -/
theorem artCivilOf_run (o : Oracle σ) {b : Word} {s1 : PancakeState σ} (z : Nat) (hz : z < 2 ^ 30)
    (hdays : s1.locals "days" = some (BitVec.ofNat 64 z)) (hb : s1.baseAddr = b) (hpow : PowIn b s1.memory)
    (hcov : Analyzer.Covers SessionLayout.size s1.memaddrs b) (hdiv : DivOk o b s1.code) :
    ∃ k, Lower.lowerStmtsFold News.ArticleProg.artCivilOf.body = some k ∧
      SafeR o (fun s => s = s1) k (fun v m => v = BitVec.ofNat 64 (civilWord z) ∧ m = s1.memory) (fun _ => False) := by
  obtain ⟨dbody, hdcode, hdsafe⟩ := hdiv
  -- the values, as `ArticleSpec.civilFromDays` has them
  obtain ⟨zz, hzz⟩ : ∃ v, v = z + 719468 := ⟨_, rfl⟩
  obtain ⟨era, hera⟩ : ∃ v, v = zz / 146097 := ⟨_, rfl⟩
  obtain ⟨doe, hdoe⟩ : ∃ v, v = zz - era * 146097 := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ v, v = doe / 1460 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ v, v = doe / 36524 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ v, v = doe / 146096 := ⟨_, rfl⟩
  obtain ⟨yoe, hyoe⟩ : ∃ v, v = (doe - a1 + a2 - a3) / 365 := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ v, v = yoe / 4 := ⟨_, rfl⟩
  obtain ⟨b2, hb2⟩ : ∃ v, v = yoe / 100 := ⟨_, rfl⟩
  obtain ⟨doy, hdoy⟩ : ∃ v, v = doe - (365 * yoe + b1 - b2) := ⟨_, rfl⟩
  obtain ⟨mp, hmp⟩ : ∃ v, v = (5 * doy + 2) / 153 := ⟨_, rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ v, v = (153 * mp + 2) / 5 := ⟨_, rfl⟩
  obtain ⟨dy, hdy⟩ : ∃ v, v = doy - c1 + 1 := ⟨_, rfl⟩
  obtain ⟨mo, hmo⟩ : ∃ v, v = (if mp < 10 then mp + 3 else mp - 9) := ⟨_, rfl⟩
  obtain ⟨yr, hyr⟩ : ∃ v, v = (if mo ≤ 2 then yoe + era * 400 + 1 else yoe + era * 400) := ⟨_, rfl⟩
  have hcw : civilWord z = yr * 512 + mo * 32 + dy := by
    simp only [civilWord, News.ArticleSpec.civilFromDays]
    subst hzz hera hdoe ha1 ha2 ha3 hyoe hb1 hb2 hdoy hmp hc1 hdy hmo hyr
    split <;> simp_all
  have g1 : doe < 146097 ∧ era * 146097 ≤ zz ∧ zz < 2 ^ 31 := by subst hzz hera hdoe; omega
  have g7 : 365 * yoe + b1 - b2 ≤ doe := by
    subst ha1 ha2 ha3 hyoe hb1 hb2; exact cal_doe doe g1.1
  have g2 : a1 ≤ doe ∧ a3 ≤ doe - a1 + a2 ∧ yoe < 400 ∧ b2 ≤ 365 * yoe + b1 ∧ c1 ≤ doy ∧ doy ≤ doe := by
    subst ha1 ha2 ha3 hyoe hb1 hb2 hdoy hmp hc1; omega
  have hmp' : mp < 2 ^ 20 := by subst hmp; omega
  have hmo' : mo < 2 ^ 20 := by subst hmo; split <;> omega
  have hdy' : dy < 2 ^ 20 := by subst hdy; omega
  have hyr' : yr < 2 ^ 30 := by subst hyr; split <;> omega
  -- a call of `artDiv`
  have cdiv : ∀ (xs : List (String × Value)) (rt : String) (ex : Syntax.PExpr) (EX : PancakeExp) (x d : Nat),
      Lower.lowerExp ex = some EX → (∀ s, CState s1 xs s → eval s EX = some (BitVec.ofNat 64 x)) → x < 2 ^ 62 →
      1 ≤ d → d ≤ 2 ^ 62 → rt ∉ xs.map Prod.fst →
      Frag o [.call rt "artDiv" [ex, Syntax.n d]] (CState s1 xs) (CState s1 ((rt, BitVec.ofNat 64 (x / d)) :: xs)) :=
    fun xs rt ex EX x d hex hev hx hd1 hd2 hrt =>
      ccall_frag o (args := [EX, .const (BitVec.ofNat 64 d)]) (by simp [Lower.lowerArgs, hex, Syntax.n, Lower.lowerExp])
        (ps := ["x", "d"]) (by decide) hdcode (vs := [BitVec.ofNat 64 x, BitVec.ofNat 64 d]) rfl
        (fun s h => by simp [evalArgs, eval, hev s h])
        (fun s h => hdsafe x d _ (by simp) rfl (h.2.2.2.1.trans hb)
          (by show PowIn b s.memory; rw [h.1]; exact hpow) (h.2.1 ▸ hcov) h.2.2.2.2.1 hx hd1 hd2) hrt
  have hmul : ∀ x y : Nat, BitVec.ofNat 64 x * BitVec.ofNat 64 y = BitVec.ofNat 64 (x * y) :=
    fun x y => (BitVec.ofNat_mul x y).symm
  have hadd : ∀ x y : Nat, BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 (x + y) :=
    fun x y => (BitVec.ofNat_add x y).symm
  have hsub : ∀ x y : Nat, y ≤ x → x < 2 ^ 64 → BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (x - y) :=
    fun x y h1 h2 => SessionCheck.sub_small x y h1 h2
  -- the statements, in turn
  let x0 : List (String × Value) := [("days", BitVec.ofNat 64 z)]
  have f0 : Frag o [.dec "a" (Syntax.atOff .base News.AbnfProg.areaOffset)] (CState s1 x0)
      (CState s1 (("a", b + BitVec.ofNat 64 News.AbnfProg.areaOffset) :: x0)) :=
    cval_frag o (at_lower (by decide)) (fun s h => by simp [eval, h.2.2.2.1, hb]) (by simp [x0])
  let x1 := ("a", b + BitVec.ofNat 64 News.AbnfProg.areaOffset) :: x0
  have f1 : Frag o [.dec "z" (Syntax.eAdd (Syntax.v "days") (Syntax.n 719468))] (CState s1 x1)
      (CState s1 (("z", BitVec.ofNat 64 zz) :: x1)) :=
    cval_frag o rfl (fun s h => by
      simp only [eval, localsAre_get h.2.2.2.2.2 (show ("days", BitVec.ofNat 64 z) ∈ x1 by simp [x1, x0])]
      rw [hadd, hzz]) (by simp [x1, x0])
  let x2 := ("z", BitVec.ofNat 64 zz) :: x1
  have f2 := cdiv x2 "era" (Syntax.v "z") (.var "z") zz 146097 rfl
    (fun s h => localsAre_get h.2.2.2.2.2 (by simp [x2])) (by omega) (by decide) (by decide) (by simp [x2, x1, x0])
  rw [← hera] at f2
  let x3 := ("era", BitVec.ofNat 64 era) :: x2
  have f3 : Frag o [.dec "doe" (Syntax.eSub (Syntax.v "z") (Syntax.eMul (Syntax.v "era") (Syntax.n 146097)))]
      (CState s1 x3) (CState s1 (("doe", BitVec.ofNat 64 doe) :: x3)) :=
    cval_frag o rfl (fun s h => by
      simp only [eval, localsAre_get h.2.2.2.2.2 (show ("z", BitVec.ofNat 64 zz) ∈ x3 by simp [x3, x2]),
        localsAre_get h.2.2.2.2.2 (show ("era", BitVec.ofNat 64 era) ∈ x3 by simp [x3])]
      rw [hmul, hsub _ _ g1.2.1 (by omega), hdoe]) (by simp [x3, x2, x1, x0])
  let x4 := ("doe", BitVec.ofNat 64 doe) :: x3
  have f4 := cdiv x4 "a1" (Syntax.v "doe") (.var "doe") doe 1460 rfl
    (fun s h => localsAre_get h.2.2.2.2.2 (by simp [x4])) (by omega) (by decide) (by decide) (by simp [x4, x3, x2, x1, x0])
  rw [← ha1] at f4
  let x5 := ("a1", BitVec.ofNat 64 a1) :: x4
  have f5 := cdiv x5 "a2" (Syntax.v "doe") (.var "doe") doe 36524 rfl
    (fun s h => localsAre_get h.2.2.2.2.2 (by simp [x5, x4])) (by omega) (by decide) (by decide) (by simp [x5, x4, x3, x2, x1, x0])
  rw [← ha2] at f5
  let x6 := ("a2", BitVec.ofNat 64 a2) :: x5
  have f6 := cdiv x6 "a3" (Syntax.v "doe") (.var "doe") doe 146096 rfl
    (fun s h => localsAre_get h.2.2.2.2.2 (by simp [x6, x5, x4])) (by omega) (by decide) (by decide)
    (by simp [x6, x5, x4, x3, x2, x1, x0])
  rw [← ha3] at f6
  let x7 := ("a3", BitVec.ofNat 64 a3) :: x6
  have f7 := cdiv x7 "yoe" (Syntax.eSub (Syntax.eAdd (Syntax.eSub (Syntax.v "doe") (Syntax.v "a1")) (Syntax.v "a2"))
      (Syntax.v "a3")) (.op .sub (.op .add (.op .sub (.var "doe") (.var "a1")) (.var "a2")) (.var "a3"))
    (doe - a1 + a2 - a3) 365 rfl (fun s h => by
      simp only [eval, localsAre_get h.2.2.2.2.2 (show ("doe", BitVec.ofNat 64 doe) ∈ x7 by simp [x7, x6, x5, x4]),
        localsAre_get h.2.2.2.2.2 (show ("a1", BitVec.ofNat 64 a1) ∈ x7 by simp [x7, x6, x5]),
        localsAre_get h.2.2.2.2.2 (show ("a2", BitVec.ofNat 64 a2) ∈ x7 by simp [x7, x6]),
        localsAre_get h.2.2.2.2.2 (show ("a3", BitVec.ofNat 64 a3) ∈ x7 by simp [x7])]
      rw [hsub _ _ g2.1 (by omega), hadd, hsub _ _ g2.2.1 (by omega)]) (by omega) (by decide) (by decide)
    (by simp [x7, x6, x5, x4, x3, x2, x1, x0])
  rw [← hyoe] at f7
  let x8 := ("yoe", BitVec.ofNat 64 yoe) :: x7
  have f8 := cdiv x8 "b1" (Syntax.v "yoe") (.var "yoe") yoe 4 rfl
    (fun s h => localsAre_get h.2.2.2.2.2 (by simp [x8])) (by omega) (by decide) (by decide)
    (by simp [x8, x7, x6, x5, x4, x3, x2, x1, x0])
  rw [← hb1] at f8
  let x9 := ("b1", BitVec.ofNat 64 b1) :: x8
  have f9 := cdiv x9 "b2" (Syntax.v "yoe") (.var "yoe") yoe 100 rfl
    (fun s h => localsAre_get h.2.2.2.2.2 (by simp [x9, x8])) (by omega) (by decide) (by decide)
    (by simp [x9, x8, x7, x6, x5, x4, x3, x2, x1, x0])
  rw [← hb2] at f9
  let x10 := ("b2", BitVec.ofNat 64 b2) :: x9
  have f10 : Frag o [.dec "doy" (Syntax.eSub (Syntax.v "doe") (Syntax.eSub (Syntax.eAdd (Syntax.eMul (Syntax.n 365)
      (Syntax.v "yoe")) (Syntax.v "b1")) (Syntax.v "b2")))] (CState s1 x10)
      (CState s1 (("doy", BitVec.ofNat 64 doy) :: x10)) :=
    cval_frag o rfl (fun s h => by
      simp only [eval, localsAre_get h.2.2.2.2.2 (show ("doe", BitVec.ofNat 64 doe) ∈ x10 by simp [x10, x9, x8, x7, x6, x5, x4]),
        localsAre_get h.2.2.2.2.2 (show ("yoe", BitVec.ofNat 64 yoe) ∈ x10 by simp [x10, x9, x8]),
        localsAre_get h.2.2.2.2.2 (show ("b1", BitVec.ofNat 64 b1) ∈ x10 by simp [x10, x9]),
        localsAre_get h.2.2.2.2.2 (show ("b2", BitVec.ofNat 64 b2) ∈ x10 by simp [x10])]
      rw [hmul, hadd, hsub _ _ g2.2.2.2.1 (by omega), hsub _ _ g7 (by omega), hdoy]) (by simp [x10, x9, x8, x7, x6, x5,
        x4, x3, x2, x1, x0])
  let x11 := ("doy", BitVec.ofNat 64 doy) :: x10
  have f11 := cdiv x11 "mp" (Syntax.eAdd (Syntax.eMul (Syntax.n 5) (Syntax.v "doy")) (Syntax.n 2))
    (.op .add (.mul (.const (BitVec.ofNat 64 5)) (.var "doy")) (.const (BitVec.ofNat 64 2))) (5 * doy + 2) 153 rfl
    (fun s h => by simp only [eval, localsAre_get h.2.2.2.2.2 (show ("doy", BitVec.ofNat 64 doy) ∈ x11 by simp [x11])]
                   rw [hmul, hadd]) (by omega) (by decide) (by decide)
    (by simp [x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0])
  rw [← hmp] at f11
  let x12 := ("mp", BitVec.ofNat 64 mp) :: x11
  have f12 := cdiv x12 "c1" (Syntax.eAdd (Syntax.eMul (Syntax.n 153) (Syntax.v "mp")) (Syntax.n 2))
    (.op .add (.mul (.const (BitVec.ofNat 64 153)) (.var "mp")) (.const (BitVec.ofNat 64 2))) (153 * mp + 2) 5 rfl
    (fun s h => by simp only [eval, localsAre_get h.2.2.2.2.2 (show ("mp", BitVec.ofNat 64 mp) ∈ x12 by simp [x12])]
                   rw [hmul, hadd]) (by omega) (by decide) (by decide)
    (by simp [x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0])
  rw [← hc1] at f12
  let x13 := ("c1", BitVec.ofNat 64 c1) :: x12
  have f13 : Frag o [.dec "dy" (Syntax.eAdd (Syntax.eSub (Syntax.v "doy") (Syntax.v "c1")) (Syntax.n 1))]
      (CState s1 x13) (CState s1 (("dy", BitVec.ofNat 64 dy) :: x13)) :=
    cval_frag o rfl (fun s h => by
      simp only [eval, localsAre_get h.2.2.2.2.2 (show ("doy", BitVec.ofNat 64 doy) ∈ x13 by simp [x13, x12, x11]),
        localsAre_get h.2.2.2.2.2 (show ("c1", BitVec.ofNat 64 c1) ∈ x13 by simp [x13])]
      rw [hsub _ _ g2.2.2.2.2.1 (by omega), hadd, hdy]) (by simp [x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2,
        x1, x0])
  let x14 := ("dy", BitVec.ofNat 64 dy) :: x13
  -- the month: three on from `mp`, nine back past ten
  have f14 : Frag o [.dec "mo" (Syntax.eAdd (Syntax.v "mp") (Syntax.n 3))] (CState s1 x14)
      (CState s1 (("mo", BitVec.ofNat 64 (mp + 3)) :: x14)) :=
    cval_frag o rfl (fun s h => by
      simp only [eval, localsAre_get h.2.2.2.2.2 (show ("mp", BitVec.ofNat 64 mp) ∈ x14 by simp [x14, x13, x12])]
      rw [hadd]) (by simp [x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0])
  have hmo14 : "mo" ∉ x14.map Prod.fst := by simp [x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0]
  have f15 : Frag o [SessionStore.ifs (Syntax.eLe (Syntax.n 10) (Syntax.v "mp"))
      [.assign "mo" (Syntax.eSub (Syntax.v "mp") (Syntax.n 9))]]
      (CState s1 (("mo", BitVec.ofNat 64 (mp + 3)) :: x14)) (CState s1 (("mo", BitVec.ofNat 64 mo) :: x14)) := by
    refine frag_oneR (a := .cond (.cmp .notLess (.var "mp") (.const (BitVec.ofNat 64 10)))
      (.assign "mo" (.op .sub (.var "mp") (.const (BitVec.ofNat 64 9)))) .skip) rfl rfl cstate_clock fun R => ?_
    have hmpv : ∀ s, CState s1 (("mo", BitVec.ofNat 64 (mp + 3)) :: x14) s →
        s.locals "mp" = some (BitVec.ofNat 64 mp) := fun s h => localsAre_get h.2.2.2.2.2 (by simp [x14, x13, x12])
    have hc : ∀ s, CState s1 (("mo", BitVec.ofNat 64 (mp + 3)) :: x14) s →
        eval s (.cmp .notLess (.var "mp") (.const (BitVec.ofNat 64 10))) = some (if mp < 10 then 0 else 1) := by
      intro s h
      simp only [eval, hmpv s h, WpBytes.signedLt_small (a := mp) (b := 10) (by omega) (by decide)]
      by_cases e : mp < 10 <;> simp [e]
    by_cases e : mp < 10
    · have : mo = mp + 3 := by rw [hmo, if_pos e]
      subst this
      exact WpRet.cond (fun s h => ⟨_, hc s h⟩) (fun s ⟨h, hne⟩ => absurd (hc s h) (by simp [e]; exact hne))
        (conseq (WpRet.skip o _ R) (fun s h => h.1) (fun _ _ h => h) (fun _ h => h))
    · have : mo = mp - 9 := by rw [hmo, if_neg e]
      refine WpRet.cond (fun s h => ⟨_, hc s h⟩) (WpRet.assign fun s ⟨h, _⟩ => ⟨BitVec.ofNat 64 (mp - 9),
        BitVec.ofNat 64 (mp + 3), by simp only [eval, hmpv s h]; rw [hsub _ _ (by omega) (by omega)],
        localsAre_get h.2.2.2.2.2 (List.mem_cons_self ..), ?_⟩)
        (fun s ⟨h, he⟩ => absurd he (by rw [hc s h]; simp [e]))
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [setLocal, this]
      · exact localsAre_set (fun q hq => h.2.2.2.2.2 q (List.mem_cons_of_mem _ hq)) hmo14 _ p hp
  -- the year: one on in January and February
  let x15 := ("mo", BitVec.ofNat 64 mo) :: x14
  have f16 : Frag o [.dec "yr" (Syntax.eAdd (Syntax.v "yoe") (Syntax.eMul (Syntax.v "era") (Syntax.n 400)))]
      (CState s1 x15) (CState s1 (("yr", BitVec.ofNat 64 (yoe + era * 400)) :: x15)) :=
    cval_frag o rfl (fun s h => by
      simp only [eval, localsAre_get h.2.2.2.2.2 (show ("yoe", BitVec.ofNat 64 yoe) ∈ x15 by simp [x15, x14, x13, x12, x11,
        x10, x9, x8]), localsAre_get h.2.2.2.2.2 (show ("era", BitVec.ofNat 64 era) ∈ x15 by simp [x15, x14, x13, x12, x11, x10,
        x9, x8, x7, x6, x5, x4, x3])]
      rw [hmul, hadd]) (by simp [x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0])
  have hyr15 : "yr" ∉ x15.map Prod.fst := by simp [x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0]
  have f17 : Frag o [SessionStore.ifs (Syntax.eLe (Syntax.v "mo") (Syntax.n 2)) [SessionStore.inc "yr"]]
      (CState s1 (("yr", BitVec.ofNat 64 (yoe + era * 400)) :: x15)) (CState s1 (("yr",
          BitVec.ofNat 64 yr) :: x15)) := by
    refine frag_oneR (a := .cond (.cmp .notLess (.const (BitVec.ofNat 64 2)) (.var "mo"))
      (.assign "yr" (.op .add (.var "yr") (.const (BitVec.ofNat 64 1)))) .skip) rfl rfl cstate_clock fun R => ?_
    have hmov : ∀ s, CState s1 (("yr", BitVec.ofNat 64 (yoe + era * 400)) :: x15) s →
        s.locals "mo" = some (BitVec.ofNat 64 mo) := fun s h => localsAre_get h.2.2.2.2.2 (by simp [x15])
    have hc : ∀ s, CState s1 (("yr", BitVec.ofNat 64 (yoe + era * 400)) :: x15) s →
        eval s (.cmp .notLess (.const (BitVec.ofNat 64 2)) (.var "mo")) = some (if mo ≤ 2 then 1 else 0) := by
      intro s h
      simp only [eval, hmov s h, WpBytes.signedLt_small (a := 2) (b := mo) (by decide) (by omega)]
      by_cases e : mo ≤ 2 <;> simp [e] <;> omega
    by_cases e : mo ≤ 2
    · have : yr = yoe + era * 400 + 1 := by rw [hyr, if_pos e]
      refine WpRet.cond (fun s h => ⟨_, hc s h⟩) (WpRet.assign fun s ⟨h, _⟩ => ⟨BitVec.ofNat 64 yr,
        BitVec.ofNat 64 (yoe + era * 400), by simp only [eval, localsAre_get h.2.2.2.2.2 (List.mem_cons_self ..)]; rw [hadd, this],
        localsAre_get h.2.2.2.2.2 (List.mem_cons_self ..), ?_⟩) (fun s ⟨h, he⟩ => absurd he (by rw [hc s h]; simp [e]))
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · simp [setLocal]
      · exact localsAre_set (fun q hq => h.2.2.2.2.2 q (List.mem_cons_of_mem _ hq)) hyr15 _ p hp
    · have : yr = yoe + era * 400 := by rw [hyr, if_neg e]
      rw [this]
      exact WpRet.cond (fun s h => ⟨_, hc s h⟩) (fun s ⟨h, hne⟩ => absurd (hc s h) (by simp [e]; exact hne))
        (conseq (WpRet.skip o _ R) (fun s h => h.1) (fun _ _ h => h) (fun _ h => h))
  let x17 := ("yr", BitVec.ofNat 64 yr) :: x15
  -- the word returned
  have hret : SafeR o (CState s1 x17) (.ret (.op .add (.op .add (.mul (.var "yr") (.const (BitVec.ofNat 64 512)))
      (.mul (.var "mo") (.const (BitVec.ofNat 64 32)))) (.var "dy")))
      (fun v m => v = BitVec.ofNat 64 (civilWord z) ∧ m = s1.memory) (fun _ => False) :=
    WpRet.ret fun s h => ⟨_, by
      simp only [eval, localsAre_get h.2.2.2.2.2 (show ("yr", BitVec.ofNat 64 yr) ∈ x17 by simp [x17]),
        localsAre_get h.2.2.2.2.2 (show ("mo", BitVec.ofNat 64 mo) ∈ x17 by simp [x17, x15]),
        localsAre_get h.2.2.2.2.2 (show ("dy", BitVec.ofNat 64 dy) ∈ x17 by simp [x17, x15, x14])]
      rw [hmul, hmul, hadd, hadd], by rw [hcw], h.1⟩
  have hall := frag_append f0 (frag_append f1 (frag_append f2 (frag_append f3 (frag_append f4 (frag_append f5
    (frag_append f6 (frag_append f7 (frag_append f8 (frag_append f9 (frag_append f10 (frag_append f11
    (frag_append f12 (frag_append f13 (frag_append f14 (frag_append f15 (frag_append f16 f17))))))))))))))))
  obtain ⟨k, hk, hks⟩ := hall _ _ _ (fun _ _ _ h _ => h) hret
  refine ⟨k, ?_, fun s hs => hks s ?_⟩
  · exact (Block.fold_split _ [.ret (Syntax.eAdd (Syntax.eAdd (Syntax.eMul (Syntax.v "yr") (Syntax.n 512))
      (Syntax.eMul (Syntax.v "mo") (Syntax.n 32))) (Syntax.v "dy"))] (by simp) rfl).trans hk
  · subst hs
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun p hp => by simp [x0] at hp; subst hp; exact hdays⟩

/-- **`artCivilOf` as a code holds it** keeps its contract when `artDiv` keeps its own. -/
theorem civilOk_of (o : Oracle σ) {b : Word} {code : String → Option (List String × PancakeProg)}
    (hcode : code "artCivilOf" = some (["days"], (Lower.lower News.ArticleProg.artCivilOf).getD .skip))
    (hdiv : DivOk o b code) : CivilOk o b code :=
  ⟨_, hcode, fun z s1 hd hb hpow hcov hc hz => by
    obtain ⟨k, hk, hs⟩ := artCivilOf_run o z hz hd hb hpow hcov (hc ▸ hdiv)
    simp only [Lower.lower, hk, Option.getD_some]
    exact hs⟩

/-- **`dateText` as a code holds it** keeps its contract when `artDiv` and `artCivilOf` keep theirs. -/
theorem dateOk_of (o : Oracle σ) {b : Word} {code : String → Option (List String × PancakeProg)} {secs : Nat}
    (hsecs : secs < 2 ^ 40)
    (hcode : code "dateText" = some (["c", "o"], (Lower.lower Session.dateText).getD .skip))
    (hdiv : DivOk o b code) (hciv : CivilOk o b code) : DateOk o b secs code :=
  ⟨_, hcode, fun c ofs s1 he hc hofs => by
    obtain ⟨k, hk, hs⟩ := dateText_run o he hofs hsecs (hc ▸ hdiv) (hc ▸ hciv)
    simp only [Lower.lower, hk, Option.getD_some]
    exact hs⟩

/-! ### Every reply `connText` has a branch for -/

/-- DATE's digits fit its reply: the year has at most ten. -/
theorem dateBytes_length (secs : Nat) (hs : secs < 2 ^ 40) : (dateBytes secs).length ≤ 60 := by
  obtain ⟨-, h2, -⟩ := civil_range (secs / 86400) (by omega)
  have := numDigits_le_ten _ (Nat.lt_trans h2 (by decide))
  rw [dateBytes_eq secs hs]
  simp only [List.length_append, twoDigits, List.length_cons, List.length_nil, decimal_length]
  omega

/-- A reply whose text ignores its argument, as `fixedBranches` names it. -/
def fixedRep : CommandSpec.Reply → CommandSpec.Reply
  | .active _ => .active none
  | .authUser _ => .authUser []
  | r => r

theorem fixedRep_code (r : CommandSpec.Reply) : Session.replyCode (fixedRep r) = Session.replyCode r := by
  cases r <;> rfl

theorem fixedRep_text (i : CommandSpec.Identity) (r : CommandSpec.Reply) :
    CommandSpec.text i (fixedRep r) = CommandSpec.text i r := by
  cases r <;> rfl

/-- What the reply `r` asks of the session's words besides `TextPre`: a reply of texts, a branch of its own;
STAT's article; GROUP's and LISTGROUP's group; DATE's seconds with `dateText` as the code holds it, at those seconds
(`dateOk_of` gives it the session's `dateText` at every second). -/
def ReplyIn (o : Oracle σ) (b : Word) (c : Nat) (s0 : PancakeState σ) (r : CommandSpec.Reply) : Prop :=
  (∃ j, (fixedRep r, j) ∈ fixedBranches) ∨ (∃ n id, r = .stat n id ∧ StatIn b n id s0) ∨
    (∃ count low high g sg, (r = .selected count low high g ∨ ∃ lo hi, r = .listed count low high g lo hi) ∧
      ListedIn b c count low high sg g s0) ∨
    ∃ secs, r = .time (dateBytes secs) ∧ secs < 2 ^ 40 ∧
      s0.memory (b + BitVec.ofNat 64 (ownOff + ownWall)) = BitVec.ofNat 64 secs ∧ PowIn b s0.memory ∧
      DateOk o b secs s0.code

/-- **`connText` writes the text of every reply it has a branch for**, if it returns. -/
theorem connText_reply (o : Oracle σ) {b : Word} {c : Nat} {i : CommandSpec.Identity} {s0 : PancakeState σ}
    (hpre : TextPre b c i s0) {r : CommandSpec.Reply} (hr : ReplyIn o b c s0 r) :
    ∃ k, Lower.lowerStmtsFold Session.connText.body = some k ∧
      SafeR o (TEntry b c (Session.replyCode r) s0) k
        (TextRet b c (CommandSpec.text i r) s0.memaddrs s0.be s0.memory) (fun _ => False) := by
  rcases hr with ⟨j, hj⟩ | ⟨n, id, rfl, hs⟩ | ⟨count, low, high, g, sg, hr, hl⟩ | ⟨secs, rfl, hs, hw, hp, hd⟩
  · have := connText_fixed o hpre hj
    rwa [fixedRep_code, fixedRep_text] at this
  · exact connText_stat o hpre hs
  · exact connText_listed o hpre hl hr
  · exact connText_time o hpre hw hp hd (dateBytes_length secs hs)

/-! ### The premises can hold -/

/-- Division by subtraction: a body keeping `artDiv`'s contract, which asks nothing of how long it runs. -/
def divW : PancakeProg :=
  .dec "q" (.const 0) (.seq (.while_ (.cmp .notLess (.var "x") (.var "d"))
    (.seq (.assign "x" (.op .sub (.var "x") (.var "d"))) (.assign "q" (.op .add (.var "q") (.const 1)))))
    (.ret (.var "q")))

theorem divW_run (o : Oracle σ) (x d : Nat) (s1 : PancakeState σ) (hx : s1.locals "x" = some (BitVec.ofNat 64 x))
    (hd : s1.locals "d" = some (BitVec.ofNat 64 d)) (hx62 : x < 2 ^ 62) (hd1 : 1 ≤ d) (hd62 : d ≤ 2 ^ 62) :
    SafeR o (fun s => s = s1) divW (fun v m => v = BitVec.ofNat 64 (x / d) ∧ m = s1.memory) (fun _ => False) := by
  let J : Nat → Nat → Assn σ := fun q r s => s.memory = s1.memory ∧ s.locals "d" = some (BitVec.ofNat 64 d) ∧
    q * d + r = x ∧ s.locals "q" = some (BitVec.ofNat 64 q) ∧ s.locals "x" = some (BitVec.ofNat 64 r)
  let I : Assn σ := fun s => ∃ q r, J q r s
  have hI : Safe.ClockFree I := fun _ _ h => h
  have hrx : ∀ q r, q * d + r = x → r ≤ x := fun q r h => by
    have : 0 ≤ q * d := Nat.zero_le _
    omega
  have hqx : ∀ q r, q * d + r = x → q ≤ x := fun q r h => by
    have : q ≤ q * d := Nat.le_mul_of_pos_right q hd1
    omega
  have hc : ∀ q r s, J q r s → eval s (.cmp .notLess (.var "x") (.var "d")) = some (if r < d then 0 else 1) := by
    intro q r s ⟨_, hds, hqr, _, hr⟩
    have := hrx q r hqr
    simp only [eval, hr, hds, WpBytes.signedLt_small (a := r) (b := d) (by omega) (by omega)]
    by_cases e : r < d <;> simp [e]
  refine dec (P' := I) (Q' := fun _ => False) (fun s hs => ⟨0, rfl, ?_⟩) ?_ (fun _ _ _ h => h.elim)
  · subst hs
    exact ⟨0, x, rfl, by simp [setLocal, hd], by simp, by simp [setLocal], by simp [setLocal, hx]⟩
  refine seq (WpRet.while_ (fun s ⟨q, r, h⟩ => ⟨_, hc q r s h⟩) ?_ hI) ?_ (fun _ _ h => h)
  · rintro s ⟨⟨q, r, h⟩, hne⟩
    have hdr : d ≤ r := by
      by_cases e : r < d
      · exact absurd (by rw [hc q r s h, if_pos e]) hne
      · omega
    have := hrx q r h.2.2.1
    have := hqx q r h.2.2.1
    refine WpRet.seq (M := fun u => u.memory = s1.memory ∧ u.locals "d" = some (BitVec.ofNat 64 d) ∧
        u.locals "q" = some (BitVec.ofNat 64 q) ∧ u.locals "x" = some (BitVec.ofNat 64 (r - d)))
      (P := fun u => J q r u)
      (WpRet.assign fun u ⟨hm, hds, _, hq, hr⟩ => ⟨BitVec.ofNat 64 (r - d), BitVec.ofNat 64 r,
        by simp only [eval, hr, hds]; rw [SessionCheck.sub_small r d hdr (by omega)], hr,
        hm, by simp [setLocal, hds], by simp [setLocal, hq], by simp [setLocal]⟩)
      (WpRet.assign fun u ⟨hm, hds, hq, hr⟩ => ⟨BitVec.ofNat 64 (q + 1), BitVec.ofNat 64 q,
        by simp [eval, hq, BitVec.ofNat_add], hq, q + 1, r - d, hm, by simp [setLocal, hds],
        by rw [Nat.add_mul]; omega, by simp [setLocal], by simp [setLocal, hr]⟩)
      (fun _ _ h => h) s h
  · exact WpRet.ret fun s ⟨⟨q, r, hm, hds, hqr, hq, hr⟩, he⟩ => ⟨BitVec.ofNat 64 q, by simp [eval, hq], by
      have hrd : r < d := by
        by_cases e : r < d
        · exact e
        · exact absurd he (by rw [hc q r s ⟨hm, hds, hqr, hq, hr⟩, if_neg e]; simp)
      rw [← hqr, show (q * d + r) / d = q from by
        rw [Nat.add_comm, Nat.add_mul_div_right r q (by omega), Nat.div_eq_of_lt hrd, Nat.zero_add]], hm⟩

/-- A code holding `dateText`, `artCivilOf`, and `divW` as `artDiv`. -/
def wCode (f : String) : Option (List String × PancakeProg) :=
  if f = "artDiv" then some (["x", "d"], divW)
  else if f = "artCivilOf" then some (["days"], (Lower.lower News.ArticleProg.artCivilOf).getD .skip)
  else if f = "dateText" then some (["c", "o"], (Lower.lower Session.dateText).getD .skip) else none

theorem divOk_witness : DivOk (σ := Unit) Oracle.idle wb wCode :=
  ⟨divW, rfl, fun x d s1 hx hd _ _ _ _ hx62 hd1 hd62 => divW_run _ x d s1 hx hd hx62 hd1 hd62⟩

theorem civilOk_witness : CivilOk (σ := Unit) Oracle.idle wb wCode := civilOk_of _ rfl divOk_witness

theorem dateOk_witness : DateOk (σ := Unit) Oracle.idle wb wSecs wCode :=
  dateOk_of _ (by decide) rfl divOk_witness civilOk_witness

/-- The session's words at connection zero's call of `dateText` from `connText`, at place 4, with the code. -/
def wStateD : PancakeState Unit :=
  { wState with
    code := wCode
    locals := fun x => if x = "o" then some 4 else wLocals x }

theorem w_dentry : DEntry wb 0 4 wSecs wStateD where
  hb := wb_aligned
  hcc := by rw [nums.count]; decide
  hcov := w_cov
  hc := rfl
  ho := rfl
  base := rfl
  hwall := w_own_val (by decide +kernel)
  hpow := w_pow

/-- DATE's premises hold together: the identity and the texts, the seconds, the powers of two and the code. -/
theorem time_witness : TextPre wb 0 wId wStateD ∧
    ReplyIn (σ := Unit) Oracle.idle wb 0 wStateD (.time (dateBytes wSecs)) :=
  ⟨{ w_pre with hid := { w_id with } }, Or.inr (Or.inr (Or.inr ⟨wSecs, rfl, by decide, w_dentry.hwall, w_pow,
    dateOk_witness⟩))⟩

theorem dctx_witness : DCtx wb 0 wStateD wStateD := ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem dbytes_witness : DBytes wb 0 4 [] wStateD wStateD := ⟨fun _ h => absurd h (by simp), fun _ _ => rfl⟩

theorem localsAre_witness : LocalsAre [("c", 0), ("o", 4)] wStateD := fun p h => by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl <;> rfl

end DN.Server.SessionDate
