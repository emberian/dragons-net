-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleGrammar

/-!
# DN.News.ArticleTables

`artTables` as the program holds it. If it returns, the tables hold each name's place, length and lower-case bytes.
They also hold its flags and its field's rule.
-/

namespace DN.News.ArticleTables

open DN.News.ArticleSpec (Bytes)
open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Frag DN.News.AbnfProg
open DN.News.AbnfSets DN.News.FunRun DN.News.AbnfLeaves DN.News.ArticleRun
open DN.News.ScanRun (at_ vals_lookup)
open DN.News.ArticleProg (guardL setW codes)
open Syntax (v n)

variable {σ : Type}

/-! ## The body -/

/-- One entry's statements: its place and length, its flags and rule, its bytes in lower case. -/
def blk (r : ArticleSpec.Rules) (es : List String) (p : (String × Nat) × Nat) : List Syntax.PStmt :=
  [setW (ArticleProg.xNameT es + 16 * p.2) (n p.1.2), setW (ArticleProg.xNameT es + 16 * p.2 + 8) (n p.1.1.length),
   setW (ArticleProg.xFlags es + 8 * p.2) (n (ArticleProg.flagsOf r p.1.1)),
   setW (ArticleProg.xRuleT es + 8 * p.2) (n (ArticleProg.ruleOfName p.1.1))] ++
  (codes (ArticleProg.lowerS p.1.1)).zipIdx.map fun (c, i) =>
    Syntax.PStmt.storeb (Syntax.atOff (v "a") (ArticleProg.xNameBytes es + p.1.2 + i)) (n c)

/-- The entries `rest` from the `k`th on, their bytes from `o` on. -/
def blocks (r : ArticleSpec.Rules) (es : List String) : List String → Nat → Nat → List Syntax.PStmt
  | [], _, _ => []
  | s :: rest, k, o => blk r es ((s, o), k) ++ blocks r es rest (k + 1) (o + s.length)

theorem foldl_scan : ∀ (ls pre : List Nat) (o : Nat),
    ls.foldl (fun acc l => acc ++ [acc.getLast?.getD 0 + l]) (pre ++ [o]) = pre ++ List.scanl (· + ·) o ls
  | [], pre, o => by simp
  | l :: ls, pre, o => by
    rw [List.foldl_cons, List.getLast?_concat, Option.getD_some, foldl_scan ls (pre ++ [o]) (o + l),
      List.scanl_cons, List.append_assoc]
    rfl

theorem zip_scan (r : ArticleSpec.Rules) (es : List String) : ∀ (rest : List String) (k o : Nat),
    ((rest.zip (List.scanl (· + ·) o (rest.map String.length))).zipIdx k).flatMap (blk r es) =
      blocks r es rest k o
  | [], _, _ => rfl
  | s :: rest, k, o => by
    rw [List.map_cons, List.scanl_cons, List.zip_cons_cons, List.zipIdx_cons, List.flatMap_cons, zip_scan r es rest]
    rfl

theorem artTables_body (r : ArticleSpec.Rules) (es : List String) : (ArticleProg.artTables r es).body =
    [areaAt ArticleProg.ofs] ++ blocks r es es 0 0 ++
    [setW (ArticleProg.xFlags es + 8 * ArticleProg.E es) (n 0),
     setW (ArticleProg.xRuleT es + 8 * ArticleProg.E es) (n AbnfRules.optionalField), .ret (n 0)] := by
  show [areaAt ArticleProg.ofs] ++ ((es.zip _).zipIdx.flatMap (blk r es)) ++ _ = _
  rw [show (es.map String.length).foldl (fun acc l => acc ++ [acc.getLast?.getD 0 + l]) [0] =
    List.scanl (· + ·) 0 (es.map String.length) from foldl_scan _ [] 0, zip_scan]

/-! ## Stores at fixed places -/

theorem pos_ne0 {x : Nat} (h : 0 < x) : (x == 0) = false := by simp only [beq_eq_false_iff_ne]; omega

theorem at40 {A : Word} {y z : Nat} (h : y ≠ z) (hy : y < 2 ^ 40) (hz : z < 2 ^ 40) : at_ A y ≠ at_ A z :=
  DN.News.ScanRun.at_ne (by omega) (by omega) h

theorem atA_lower {x : Nat} (hx : (x == 0) = false) :
    Lower.lowerExp (Syntax.atOff (v "a") x) = some (.op .add (.var "a") (.const (BitVec.ofNat 64 x))) := by
  rw [atOff_eq hx]; rfl

/-- **A word stored** at a fixed place of the area. -/
theorem setC_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {M : Word → Word} {A : Word}
    (hla : L.lookup "a" = some A) {off c : Nat} (hoff : (off == 0) = false) (hdm : s1.memaddrs (at_ A off) = true) :
    Frag o [setW off (n c)] (RunF s1 L (· = M)) (RunF s1 L (· = upd M (at_ A off) (BitVec.ofNat 64 c))) :=
  runF_storeA o (atA_lower hoff) rfl hdm (fun u h => atA_eval (vals_lookup h.1.vals hla))
    (val := fun _ => BitVec.ofNat 64 c) (fun u h => rfl) fun m h => by rw [h]

/-- **A byte stored** at a fixed place of the area. -/
theorem putC_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {M : Word → Word} {A : Word}
    (hla : L.lookup "a" = some A) {off c : Nat} (hoff : (off == 0) = false)
    (hdm : s1.memaddrs (byteAlign (at_ A off)) = true) :
    Frag o [.storeb (Syntax.atOff (v "a") off) (n c)] (RunF s1 L (· = M))
      (RunF s1 L (· = DN.Compiler.Bytes.putByte M s1.be (at_ A off) (BitVec.ofNat 8 c))) :=
  storeb_frag o (atA_lower hoff) rfl (runF_clock _ _ _) fun u h => ⟨at_ A off, BitVec.ofNat 64 c,
    atA_eval (vals_lookup h.1.vals hla), rfl, by rw [h.1.memaddrs]; exact hdm,
    ⟨h.1.vals, h.1.memaddrs, h.1.base, h.1.code, h.1.be⟩, by
      show DN.Compiler.Bytes.putByte u.memory u.be _ _ = _
      rw [h.2, h.1.be, DN.Compiler.Bytes.setWidth_ofNat_8]⟩

/-- A byte read past the words a store changes. -/
theorem load_upd_below {A : Word} (hA8 : A.toNat % 8 = 0) {m : Word → Word} {dm : Word → Bool} {be : Bool}
    {y z : Nat} (hz : z < y / 8 * 8) (hy : y < 2 ^ 64) (w : Word) :
    memLoadByte (upd m (at_ A z) w) dm be (at_ A y) = memLoadByte m dm be (at_ A y) := by
  unfold memLoadByte
  rw [DN.News.ScanRun.align_at hA8, upd_ne _ (DN.News.ScanRun.at_ne (by omega) (by omega) (by omega))]

/-- A word below the bytes a byte store changes. -/
theorem putByte_below {A : Word} (hA8 : A.toNat % 8 = 0) {m : Word → Word} {be : Bool} {y z : Nat}
    (hz : z < y / 8 * 8) (hy : y < 2 ^ 64) (b : BitVec 8) :
    DN.Compiler.Bytes.putByte m be (at_ A y) b (at_ A z) = m (at_ A z) := by
  unfold DN.Compiler.Bytes.putByte
  rw [DN.News.ScanRun.align_at hA8, if_neg (DN.News.ScanRun.at_ne (by omega) (by omega) (by omega))]

/-- The byte stores of codes `cs`, the `i`th at `B + i`. -/
def storesB (B : Nat) (cs : List Nat) (i0 : Nat) : List Syntax.PStmt :=
  (cs.zipIdx i0).map fun (c, i) => Syntax.PStmt.storeb (Syntax.atOff (v "a") (B + i)) (n c)

/-- **Bytes stored**: codes `cs` from `B + i0` on; other bytes past `NB`, and words below it, kept. -/
theorem bytes_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {A : Word}
    (hla : L.lookup "a" = some A) (hA8 : A.toNat % 8 = 0) {NB B LIM : Nat} (hNB8 : NB % 8 = 0) (hNB : NB ≤ B)
    (hNB0 : 0 < NB) (hLIM : LIM < 2 ^ 64)
    (hdm : ∀ y, NB ≤ y → y < LIM → s1.memaddrs (byteAlign (at_ A y)) = true) :
    ∀ (cs : List Nat) (i0 : Nat) (M : Word → Word), B + i0 + cs.length ≤ LIM →
    Frag o (storesB B cs i0) (RunF s1 L (· = M)) (fun u => ∃ m, RunF s1 L (· = m) u ∧
      (∀ j (hj : j < cs.length), memLoadByte m s1.memaddrs s1.be (at_ A (B + i0 + j)) = some (BitVec.ofNat 8 cs[j])) ∧
      (∀ y, NB ≤ y → y < LIM → (y < B + i0 ∨ B + i0 + cs.length ≤ y) →
        memLoadByte m s1.memaddrs s1.be (at_ A y) = memLoadByte M s1.memaddrs s1.be (at_ A y)) ∧
      (∀ z, z < NB → m (at_ A z) = M (at_ A z)) ∧ ∀ x, (∀ y, NB ≤ y → y < LIM → x ≠ at_ A y) → m x = M x)
  | [], i0, M, _ => frag_nil o fun u h =>
    ⟨M, h, fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | c :: cs, i0, M, hL => by
    have hlc : (c :: cs).length = cs.length + 1 := rfl
    simp only [List.length_cons] at hL
    show Frag o ([_] ++ storesB B cs (i0 + 1)) _ _
    refine frag_append (putC_frag o hla (off := B + i0) (c := c) (by simp only [beq_eq_false_iff_ne]; omega)
      (hdm _ (by omega) (by omega))) ?_
    refine frag_conseq (bytes_frag o hla hA8 hNB8 hNB hNB0 hLIM hdm cs (i0 + 1) _ (by omega)) (fun _ h => h) ?_
    rintro u ⟨m, h, hb, hy, hz, hx⟩
    refine ⟨m, h, fun j hj => ?_, fun y h1 h2 h3 => ?_, fun z hz' => ?_, fun x hx' => ?_⟩
    · cases j with
      | zero =>
        rw [hy _ (by omega) (by omega) (.inl (by omega)), Nat.add_zero,
          DN.Compiler.Bytes.load_putByte_same _ _ _ _ _ (hdm _ (by omega) (by omega))]
        rfl
      | succ j =>
        rw [show B + i0 + (j + 1) = B + (i0 + 1) + j by omega]
        exact hb j (by simp only [List.length_cons] at hj; omega)
    · rw [hy y h1 h2 (by omega), DN.Compiler.Bytes.load_putByte_diff _ _ _ _ _ _
        (DN.News.ScanRun.at_ne (by omega) (by omega) (by omega))]
    · rw [hz z hz', putByte_below hA8 (by omega) (by omega)]
    · rw [hx x hx']
      unfold DN.Compiler.Bytes.putByte
      rw [DN.News.ScanRun.align_at hA8, if_neg (hx' _ (by omega) (by omega))]

/-! ## One entry -/

/-- Entry `k`'s tables: name `s` at `o`, its length, flags and rule, its bytes in lower case. -/
structure EntryAt (r : ArticleSpec.Rules) (es : List String) (A : Word) (dm : Word → Bool) (be : Bool)
    (m : Word → Word) (s : String) (o k : Nat) : Prop where
  off : m (at_ A (ArticleProg.xNameT es + 16 * k)) = BitVec.ofNat 64 o
  len : m (at_ A (ArticleProg.xNameT es + 16 * k + 8)) = BitVec.ofNat 64 s.length
  flags : m (at_ A (ArticleProg.xFlags es + 8 * k)) = BitVec.ofNat 64 (ArticleProg.flagsOf r s)
  rule : m (at_ A (ArticleProg.xRuleT es + 8 * k)) = BitVec.ofNat 64 (ArticleProg.ruleOfName s)
  bytes : ∀ i, i < s.length →
    memLoadByte m dm be (at_ A (ArticleProg.xNameBytes es + o + i)) = some (lowCodes s)[i]!

/-- The table words of entry `k`. -/
def TabW (es : List String) (k y : Nat) : Prop :=
  y = ArticleProg.xNameT es + 16 * k ∨ y = ArticleProg.xNameT es + 16 * k + 8 ∨ y = ArticleProg.xFlags es + 8 * k ∨
    y = ArticleProg.xRuleT es + 8 * k

/-- The layout of the tables, as numbers. -/
theorem lay (es : List String) :
    ArticleProg.xFlags es = ArticleProg.xFirst + 8 * (es.length + 1) ∧
    ArticleProg.xRuleT es = ArticleProg.xFirst + 16 * (es.length + 1) ∧
    ArticleProg.xNameT es = ArticleProg.xFirst + 24 * (es.length + 1) ∧
    ArticleProg.xNameBytes es = ArticleProg.xFirst + 24 * (es.length + 1) + 16 * es.length ∧
    ArticleProg.xNameBytes es + ArticleProg.nameBytes es ≤ ArticleProg.size es ∧ ArticleProg.xFirst = 576408 := by
  simp only [ArticleProg.xNameBytes, ArticleProg.xNameT, ArticleProg.xRuleT, ArticleProg.xFlags, ArticleProg.E,
    ArticleProg.size, xFirst_eq]
  refine ⟨trivial, by omega, by omega, by omega, by omega, trivial⟩

theorem blk_eq (r : ArticleSpec.Rules) (es : List String) (s : String) (o k : Nat) : blk r es ((s, o), k) =
    [setW (ArticleProg.xNameT es + 16 * k) (n o), setW (ArticleProg.xNameT es + 16 * k + 8) (n s.length),
     setW (ArticleProg.xFlags es + 8 * k) (n (ArticleProg.flagsOf r s)),
     setW (ArticleProg.xRuleT es + 8 * k) (n (ArticleProg.ruleOfName s))] ++
    storesB (ArticleProg.xNameBytes es + o) (codes (ArticleProg.lowerS s)) 0 := rfl

theorem codes_length (s : String) : (codes (ArticleProg.lowerS s)).length = s.length := by
  have := lowCodes_length s; simp only [lowCodes, List.length_map] at this; exact this

/-- **One entry's tables written**: the four words and the name's bytes; the other words and bytes kept. -/
theorem blk_frag (o : Oracle σ) {s1 : PancakeState σ} {L : List (String × Value)} {A : Word}
    (hla : L.lookup "a" = some A) (hA8 : A.toNat % 8 = 0) {r : ArticleSpec.Rules} {es : List String}
    (hsz : ArticleProg.size es < 2 ^ 40) (hT : TabDom A s1.memaddrs es) {s : String} {o0 k : Nat}
    (hk : k < es.length) (ho : o0 + s.length ≤ ArticleProg.nameBytes es) (M : Word → Word) :
    Frag o (blk r es ((s, o0), k)) (RunF s1 L (· = M)) (fun u => ∃ m, RunF s1 L (· = m) u ∧
      EntryAt r es A s1.memaddrs s1.be m s o0 k ∧
      (∀ y, y < ArticleProg.xNameBytes es → ¬TabW es k y → m (at_ A y) = M (at_ A y)) ∧
      (∀ y, ArticleProg.xNameBytes es ≤ y → y < ArticleProg.size es →
        (y < ArticleProg.xNameBytes es + o0 ∨ ArticleProg.xNameBytes es + o0 + s.length ≤ y) →
        memLoadByte m s1.memaddrs s1.be (at_ A y) = memLoadByte M s1.memaddrs s1.be (at_ A y)) ∧
      ∀ x, (∀ y, ArticleProg.xFlags es ≤ y → y < ArticleProg.size es → x ≠ at_ A y) → m x = M x) := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay es
  have hdmB : ∀ y, ArticleProg.xNameBytes es ≤ y → y < ArticleProg.size es →
      s1.memaddrs (byteAlign (at_ A y)) = true := fun y h1 h2 => by
    rw [DN.News.ScanRun.align_at hA8]; exact hT _ (by omega) (by omega) (by omega)
  rw [blk_eq]
  refine frag_append (xs := [_, _, _, _]) (frag_append (xs := [_]) (setC_frag o hla (c := o0) (pos_ne0 (by omega))
    (hT _ (by omega) (by omega) (by omega))) (frag_append (xs := [_]) (setC_frag o hla (c := s.length)
    (pos_ne0 (by omega)) (hT _ (by omega) (by omega) (by omega))) (frag_append (xs := [_]) (setC_frag o hla
    (c := ArticleProg.flagsOf r s) (pos_ne0 (by omega)) (hT _ (by omega) (by omega) (by omega)))
    (setC_frag o hla (c := ArticleProg.ruleOfName s) (pos_ne0 (by omega)) (hT _ (by omega) (by omega) (by omega))))))
    ?_
  have hNB8 : ArticleProg.xNameBytes es % 8 = 0 := by omega
  refine frag_conseq (bytes_frag o hla hA8 (NB := ArticleProg.xNameBytes es) (B := ArticleProg.xNameBytes es + o0)
    (LIM := ArticleProg.size es) hNB8 (by omega) (by omega) (by omega) hdmB (codes (ArticleProg.lowerS s)) 0 _
    (by rw [codes_length]; omega)) (fun _ h => h) ?_
  rintro u ⟨m, h, hb, hy, hz, hx⟩
  refine ⟨m, h, ⟨?_, ?_, ?_, ?_, fun i hi => ?_⟩, fun y hy1 hy2 => ?_, fun y h1 h2 h3 => ?_, fun x hx' => ?_⟩
  · rw [hz _ (by omega), upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]
  · rw [hz _ (by omega), upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]
  · rw [hz _ (by omega), upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]
  · rw [hz _ (by omega), upd_eq]
  · have hcl := codes_length s
    rw [show ArticleProg.xNameBytes es + o0 + i = ArticleProg.xNameBytes es + o0 + 0 + i by omega,
      hb i (by omega), lowCodes, getElem!_pos _ i (by simp only [List.length_map]; omega), List.getElem_map]
  · simp only [TabW, not_or] at hy2
    obtain ⟨n1, n2, n3, n4⟩ := hy2
    rw [hz _ hy1, upd_ne _ (at40 n4 (by omega) (by omega)), upd_ne _ (at40 n3 (by omega) (by omega)),
      upd_ne _ (at40 n2 (by omega) (by omega)), upd_ne _ (at40 n1 (by omega) (by omega))]
  · rw [hy y h1 h2 (by rw [codes_length]; omega), load_upd_below hA8 (by omega) (by omega),
      load_upd_below hA8 (by omega) (by omega), load_upd_below hA8 (by omega) (by omega),
      load_upd_below hA8 (by omega) (by omega)]
  · rw [hx x fun y h1 h2 => hx' y (by omega) h2, upd_ne _ (hx' _ (by omega) (by omega)),
      upd_ne _ (hx' _ (by omega) (by omega)), upd_ne _ (hx' _ (by omega) (by omega)),
      upd_ne _ (hx' _ (by omega) (by omega))]

/-! ## All entries -/

theorem setW_low {off : Nat} (hoff : (off == 0) = false) (c : Nat) : LowKK [setW off (n c)] :=
  lowKK_one rfl (by simp [Lower.lowerStmt1, setW, atA_lower hoff]; rfl)

theorem putC_low {off : Nat} (hoff : (off == 0) = false) (c : Nat) :
    LowKK [.storeb (Syntax.atOff (v "a") off) (n c)] :=
  lowKK_one rfl (by simp [Lower.lowerStmt1, atA_lower hoff]; rfl)

theorem storesB_low {B : Nat} (hB : 0 < B) : ∀ (cs : List Nat) (i0 : Nat), LowKK (storesB B cs i0)
  | [], _ => fun k => ⟨k, rfl⟩
  | c :: cs, i0 => by
    show LowKK ([_] ++ storesB B cs (i0 + 1))
    exact lowKK_append (putC_low (by simp only [beq_eq_false_iff_ne]; omega) c) (storesB_low hB cs (i0 + 1))

theorem blocks_low (r : ArticleSpec.Rules) (es : List String) : ∀ (rest : List String) (k o : Nat),
    LowKK (blocks r es rest k o)
  | [], _, _ => fun k => ⟨k, rfl⟩
  | s :: rest, k, o => by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay es
    show LowKK (blk r es ((s, o), k) ++ _)
    rw [blk_eq]
    exact lowKK_append (lowKK_append (lowKK_append (lowKK_append (lowKK_append (setW_low (pos_ne0 (by omega)) _)
      (setW_low (pos_ne0 (by omega)) _)) (setW_low (pos_ne0 (by omega)) _)) (setW_low (pos_ne0 (by omega)) _))
      (storesB_low (by omega) _ 0)) (blocks_low r es rest (k + 1) (o + s.length))

theorem tabW_ne {es : List String} {k k' : Nat} (hk : k < es.length) (hk' : k' < es.length) (hne : k ≠ k')
    {y : Nat} (h : TabW es k y) : ¬TabW es k' y := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay es
  unfold TabW at h ⊢
  omega

/-- **The entries' tables written**, those of `rest` from the `k`th on, their bytes from `o0` on. -/
theorem blocks_frag (o : Oracle σ) {R : Ret} {s1 : PancakeState σ} {L : List (String × Value)} {A : Word}
    (hla : L.lookup "a" = some A) (hA8 : A.toNat % 8 = 0) {r : ArticleSpec.Rules} {es : List String}
    (hsz : ArticleProg.size es < 2 ^ 40) (hT : TabDom A s1.memaddrs es) :
    ∀ (rest : List String) (k o0 : Nat) (M : Word → Word), k + rest.length ≤ es.length →
    o0 + (rest.map String.length).sum ≤ ArticleProg.nameBytes es →
    FragR o R (blocks r es rest k o0) (RunF s1 L (· = M)) (fun u => ∃ m, RunF s1 L (· = m) u ∧
      (∀ j (hj : j < rest.length),
        EntryAt r es A s1.memaddrs s1.be m rest[j] (o0 + ((rest.take j).map String.length).sum) (k + j)) ∧
      (∀ y, y < ArticleProg.xNameBytes es → (∀ j, j < rest.length → ¬TabW es (k + j) y) →
        m (at_ A y) = M (at_ A y)) ∧
      (∀ y, ArticleProg.xNameBytes es ≤ y → y < ArticleProg.size es → y < ArticleProg.xNameBytes es + o0 →
        memLoadByte m s1.memaddrs s1.be (at_ A y) = memLoadByte M s1.memaddrs s1.be (at_ A y)) ∧
      ∀ x, (∀ y, ArticleProg.xFlags es ≤ y → y < ArticleProg.size es → x ≠ at_ A y) → m x = M x)
  | [], k, o0, M, _, _ => fragR_of (frag_nil o fun u h =>
    ⟨M, h, fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩)
  | s :: rest, k, o0, M, h1, h2 => by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay es
    simp only [List.length_cons, List.map_cons, List.sum_cons] at h1 h2
    show FragR o R (blk r es ((s, o0), k) ++ blocks r es rest (k + 1) (o0 + s.length)) _ _
    refine fragR_append (fragR_of (blk_frag o hla hA8 hsz hT (r := r) (s := s) (o0 := o0) (k := k) (by omega)
      (by omega) M)) ?_
    refine fragR_exists (blocks_low r es rest (k + 1) (o0 + s.length)) fun m1 => ?_
    refine fragR_pure _ (fun u h => h.2) (blocks_low r es rest (k + 1) (o0 + s.length)) fun ⟨he, hw, hb, hx⟩ => ?_
    refine fragR_conseq (blocks_frag o hla hA8 hsz hT rest (k + 1) (o0 + s.length) m1 (by omega) (by omega))
      (fun u h => h.1) ?_
    rintro u ⟨m, h, hes, hw', hb', hx'⟩
    have hsl : ∀ i, i < s.length → ArticleProg.xNameBytes es + o0 + i < ArticleProg.size es := fun i hi => by omega
    have hlc : (s :: rest).length = rest.length + 1 := rfl
    refine ⟨m, h, fun j hj => ?_, fun y hy hn => ?_, fun y y1 y2 y3 => ?_, fun x hx0 => ?_⟩
    · cases j with
      | zero =>
        simp only [Nat.add_zero, List.getElem_cons_zero, List.take_zero, List.map_nil, List.sum_nil]
        refine ⟨?_, ?_, ?_, ?_, fun i hi => ?_⟩
        · rw [hw' _ (by omega) fun j' hj' => tabW_ne (k := k) (by omega) (by omega) (by omega) (.inl rfl)]
          exact he.off
        · rw [hw' _ (by omega) fun j' hj' => tabW_ne (k := k) (by omega) (by omega) (by omega) (.inr (.inl rfl))]
          exact he.len
        · rw [hw' _ (by omega) fun j' hj' => tabW_ne (k := k) (by omega) (by omega) (by omega) (.inr (.inr (.inl rfl)))]
          exact he.flags
        · rw [hw' _ (by omega) fun j' hj' =>
            tabW_ne (k := k) (by omega) (by omega) (by omega) (.inr (.inr (.inr rfl)))]
          exact he.rule
        · rw [hb' _ (by omega) (hsl i hi) (by omega)]
          exact he.bytes i hi
      | succ j =>
        have e := hes j (by simp only [List.length_cons] at hj; omega)
        simp only [List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
        rw [show k + (j + 1) = k + 1 + j by omega, show o0 + (s.length + (List.map String.length
          (List.take j rest)).sum) = o0 + s.length + (List.map String.length (List.take j rest)).sum by omega]
        exact e
    · rw [hw' y hy fun j hj => by simpa [show k + 1 + j = k + (j + 1) by omega] using hn (j + 1) (by omega),
        hw y hy (by simpa using hn 0 (by omega))]
    · rw [hb' y y1 y2 (by omega), hb y y1 y2 (.inl y3)]
    · rw [hx' x hx0, hx x hx0]

/-! ## `artTables` -/

/-- What the rules make of each entry and the rule its field is matched by; the same for no entry. -/
structure KindsAt (r : ArticleSpec.Rules) (es : List String) (A : Word) (m : Word → Word) : Prop where
  flags : ∀ k (_hk : k < es.length),
    m (at_ A (ArticleProg.xFlags es + 8 * k)) = BitVec.ofNat 64 (ArticleProg.flagsOf r es[k])
  rules : ∀ k (_hk : k < es.length),
    m (at_ A (ArticleProg.xRuleT es + 8 * k)) = BitVec.ofNat 64 (ArticleProg.ruleOfName es[k])
  flagsE : m (at_ A (ArticleProg.xFlags es + 8 * es.length)) = 0
  ruleE : m (at_ A (ArticleProg.xRuleT es + 8 * es.length)) = BitVec.ofNat 64 AbnfRules.optionalField

/-- What `artTables` leaves: 0, the tables, and every word outside them as before. -/
def TabRet (r : ArticleSpec.Rules) (es : List String) (A : Word) (dm : Word → Bool) (be : Bool)
    (m0 : Word → Word) : Ret := fun w m =>
  w = 0 ∧ TablesAt A dm be m es ∧ KindsAt r es A m ∧
    ∀ x, (∀ y, ArticleProg.xFlags es ≤ y → y < ArticleProg.size es → x ≠ at_ A y) → m x = m0 x

theorem guardL_storesB (B : Nat) : ∀ (cs : List Nat) (i0 : Nat), guardL (storesB B cs i0) = storesB B cs i0
  | [], _ => rfl
  | c :: cs, i0 => by
    show guardL ([_] ++ storesB B cs (i0 + 1)) = [_] ++ storesB B cs (i0 + 1)
    rw [DN.News.ArticleGrammar.guardL_append, guardL_storesB B cs (i0 + 1)]; rfl

theorem guardL_blocks (r : ArticleSpec.Rules) (es : List String) : ∀ (rest : List String) (k o : Nat),
    guardL (blocks r es rest k o) = blocks r es rest k o
  | [], _, _ => rfl
  | s :: rest, k, o => by
    show guardL (blk r es ((s, o), k) ++ _) = blk r es ((s, o), k) ++ _
    rw [DN.News.ArticleGrammar.guardL_append, blk_eq, DN.News.ArticleGrammar.guardL_append, guardL_storesB,
      guardL_blocks r es rest]
    rfl

theorem offOf_take (es : List String) (k : Nat) : 0 + ((es.take k).map String.length).sum = offOf es k := by
  rw [Nat.zero_add]; rfl

/-- **`artTables` writes the entries' tables**, if it returns. Each name gets its place, length and lower-case bytes,
its flags and its field's rule. The words outside the tables are kept. -/
theorem artTables_ok (o : Oracle σ) {r : ArticleSpec.Rules} {es : List String} (hsz : ArticleProg.size es < 2 ^ 40)
    {A : Word} {s1 : PancakeState σ} (hA : Area ArticleProg.ofs A s1) (hT : TabDom A s1.memaddrs es) :
    ∃ body, Lower.lower (gd (ArticleProg.artTables r es)) = some body ∧
      SafeR o (fun s => s = s1) body (TabRet r es A s1.memaddrs s1.be s1.memory) fun _ => False := by
  have hA8 := hA.hA
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay es
  refine body_of ?_
  show FragR o _ (guardL (ArticleProg.artTables r es).body) _ _
  rw [artTables_body, DN.News.ArticleGrammar.guardL_append, DN.News.ArticleGrammar.guardL_append, guardL_blocks]
  refine fragR_conseq (P0 := RunF s1 [] (· = s1.memory)) ?_ (entry_run (l := []) (fun q hq => nomatch hq) rfl)
    fun _ h => h
  obtain ⟨EA, hEA⟩ := atOff_lower ArticleProg.ofs
  refine fragR_append (fragR_append (xs := [_]) (fragR_of (runF_dec o hEA rfl (v := A) fun u h =>
    areaAt_eval hA h.1.base hEA)) (blocks_frag o (L := [("a", A)]) rfl hA8 (r := r) hsz hT es 0 0 s1.memory
    (by omega) (by simp only [ArticleProg.nameBytes]; omega))) ?_
  have hlow : LowKK [setW (ArticleProg.xFlags es + 8 * ArticleProg.E es) (n 0),
      setW (ArticleProg.xRuleT es + 8 * ArticleProg.E es) (n AbnfRules.optionalField), .ret (n 0)] :=
    lowKK_append (setW_low (pos_ne0 (by omega)) 0) (lowKK_append (setW_low (pos_ne0 (by omega)) _) (lowKK_ret rfl))
  refine fragR_exists hlow fun m => ?_
  refine fragR_pure _ (fun u h => h.2) hlow fun ⟨he, hw, hb, hx⟩ => ?_
  refine fragR_conseq ?_ (fun u h => h.1) fun _ h => h
  have hEl : ArticleProg.E es = es.length := rfl
  refine fragR_append (xs := [_]) (fragR_of (setC_frag o rfl (c := 0) (pos_ne0 (by omega))
    (hT _ (by omega) (by rw [hEl]; omega) (by rw [hEl]; omega)))) ?_
  refine fragR_append (xs := [_]) (fragR_of (setC_frag o rfl (c := AbnfRules.optionalField) (pos_ne0 (by omega))
    (hT _ (by omega) (by rw [hEl]; omega) (by rw [hEl]; omega)))) ?_
  refine fragR_ret o rfl fun u h => ⟨0, rfl, rfl, ?_, ?_, ?_⟩
  all_goals rw [h.2, hEl]
  · refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
    · have := (he k hk).off
      rw [Nat.zero_add, Nat.zero_add] at this
      rw [upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega))]
      exact this
    · have := (he k hk).len
      rw [Nat.zero_add] at this
      rw [upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega))]
      exact this
    · have := (he k hk).bytes i hi
      rw [offOf_take] at this
      have hof := offOf_le es hk
      rw [load_upd_below hA8 (by omega) (by omega), load_upd_below hA8 (by omega) (by omega)]
      exact this
  · refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, upd_eq _ _ _⟩
    · have := (he k hk).flags
      rw [Nat.zero_add] at this
      rw [upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega))]
      exact this
    · have := (he k hk).rule
      rw [Nat.zero_add] at this
      rw [upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega))]
      exact this
    · rw [upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]; rfl
  · intro x hx0
    rw [upd_ne _ (hx0 _ (by omega) (by omega)), upd_ne _ (hx0 _ (by omega) (by omega))]
    exact hx x hx0

/-! ## The entries of the rules -/

/-- The entries of the rules, as the program takes them. -/
abbrev esP : List String := ArticleProg.entries ArticleSpec.spec

/-- The entries written out, so that the kernel works them out once. -/
def esL : List String := ["Injection-Info", "Xref", "NNTP-Posting-Host", "NNTP-Posting-Date", "X-Trace",
  "X-Complaints-To", "Date-Received", "Posting-Version", "Relay-Version", "Also-Control", "Article-Names",
  "Article-Updates", "See-Also", "Disposition-Notification-To", "Control", "Supersedes", "Approved", "Date", "From",
  "Message-ID", "Newsgroups", "Path", "Subject", "Archive", "Distribution", "Expires", "Followup-To",
  "Injection-Date", "Lines", "Organization", "Summary", "User-Agent", "Keywords", "Sender", "Reply-To", "To", "Cc",
  "Bcc", "In-Reply-To", "References", "Cancel-Lock", "Cancel-Key", "MIME-Version", "Content-Type",
  "Content-Transfer-Encoding", "Comments", "Resent-Date", "Resent-From", "Resent-Sender", "Resent-To", "Resent-Cc",
  "Resent-Bcc", "Return-Path", "Received", "Resent-Message-ID"]

theorem es_eq : esP = esL := by decide +kernel

/-- Every name the rules read, in the order the entries are made of them. -/
def allNames : List String :=
  ArticleSpec.spec.injected ++ ArticleSpec.spec.traced ++ ArticleSpec.spec.deprecated ++
    ArticleSpec.spec.notOffered ++ ArticleSpec.spec.once ++ ArticleSpec.spec.required ++
    AbnfRules.fieldRules.map (·.1) ++ ArticleSpec.idFields ++ ArticleProg.dateFields ++ ArticleProg.readNames

/-- A name added to the entries unless one of them is it, read without case. -/
def addName (acc : List String) (s : String) : List String :=
  if acc.any (ArticleProg.lowerS · == ArticleProg.lowerS s) then acc else acc ++ [s]

theorem esP_eq : esP = allNames.foldl addName [] := rfl

/-- **Every name has an entry**, the same read without case. -/
theorem foldl_cover : ∀ (l acc : List String) (s : String), s ∈ acc ++ l →
    ∃ t ∈ l.foldl addName acc, ArticleProg.lowerS t = ArticleProg.lowerS s
  | [], acc, s, h => ⟨s, by simpa using h, rfl⟩
  | x :: l, acc, s, h => by
    rw [List.foldl_cons]
    have hsub : ∀ y ∈ acc, y ∈ addName acc x := fun y hy => by
      unfold addName; split
      · exact hy
      · exact List.mem_append_left _ hy
    rcases List.mem_append.1 h with h | h
    · exact foldl_cover l _ s (List.mem_append_left _ (hsub s h))
    · rcases List.mem_cons.1 h with rfl | h
      · unfold addName; split
        · rename_i hx
          obtain ⟨t, ht, e⟩ := List.any_eq_true.1 hx
          obtain ⟨t', ht', e'⟩ := foldl_cover l acc t (List.mem_append_left _ ht)
          exact ⟨t', ht', e'.trans (by simpa using e)⟩
        · exact foldl_cover l _ s (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
      · exact foldl_cover l _ s (List.mem_append_right _ h)

/-- **Every entry is a name.** -/
theorem foldl_sub : ∀ (l acc : List String) (t : String), t ∈ l.foldl addName acc → t ∈ acc ∨ t ∈ l
  | [], acc, t, h => .inl h
  | x :: l, acc, t, h => by
    rw [List.foldl_cons] at h
    rcases foldl_sub l _ t h with h | h
    · unfold addName at h; split at h
      · exact .inl h
      · rcases List.mem_append.1 h with h | h
        · exact .inl h
        · exact .inr (by rw [List.mem_singleton.1 h]; exact List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h)

theorem toLower_toNat (c : Char) :
    c.toLower.toNat = if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c.toNat + 32 else c.toNat := by
  unfold Char.toLower
  have hA : ('A'.val).toNat = 65 := rfl
  have hZ : ('Z'.val).toNat = 90 := rfl
  have hc : c.val.toNat = c.toNat := rfl
  split <;> rename_i h <;> simp only [UInt32.le_iff_toNat_le, ge_iff_le, hA, hZ, hc] at h
  · rw [if_pos h]; show (c.val + ('a'.val - 'A'.val)).toNat = _
    rw [UInt32.toNat_add, hc, show ('a'.val - 'A'.val).toNat = 32 from rfl]; omega
  · rw [if_neg h]

/-- A character below 256 in lower case is its byte in lower case. -/
theorem lowc (c : Char) (h : c.toNat < 256) :
    BitVec.ofNat 8 c.toLower.toNat = ArticleSpec.lowerB (BitVec.ofNat 8 c.toNat) := by
  unfold ArticleSpec.lowerB
  have h1 : (BitVec.ofNat 8 c.toNat).toNat = c.toNat := by simp [BitVec.toNat_ofNat]; omega
  rw [h1, toLower_toNat]
  split
  · rw [← BitVec.ofNat_add]
  · rfl

theorem names_bytes : ∀ n ∈ allNames, ∀ c ∈ n.toList, c.toNat < 256 := by decide +kernel

theorem lowerS_toList (s : String) : (ArticleProg.lowerS s).toList = s.toList.map Char.toLower := by
  simp [ArticleProg.lowerS]

theorem names_ascii : ∀ n ∈ allNames, lowCodes n = (DN.News.CommandSpec.ascii n).map ArticleSpec.lowerB := by
  intro n hn
  simp only [lowCodes, ArticleProg.codes, DN.News.CommandSpec.ascii, lowerS_toList, List.map_map]
  exact List.map_congr_left fun c hc => lowc c (names_bytes n hn c hc)

theorem names_small : ∀ n ∈ allNames, ∀ c ∈ (ArticleProg.lowerS n).toList, c.toNat < 256 := by
  intro n hn c hc
  rw [lowerS_toList, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have := names_bytes n hn d hd
  rw [toLower_toNat]; split <;> omega

theorem esP_size : ArticleProg.size esP < 2 ^ 40 := by rw [es_eq]; decide +kernel

theorem map_ofNat_inj : ∀ (l1 l2 : List Char), (∀ c ∈ l1, c.toNat < 256) → (∀ c ∈ l2, c.toNat < 256) →
    l1.map (fun c => BitVec.ofNat 8 c.toNat) = l2.map (fun c => BitVec.ofNat 8 c.toNat) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: l1, d :: l2, h1, h2, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hc := h1 c List.mem_cons_self
    have hd := h2 d List.mem_cons_self
    have e : c.toNat = d.toNat := by
      have := congrArg BitVec.toNat h.1
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at this
    rw [Char.toNat_inj.1 e, map_ofNat_inj l1 l2 (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) h.2]

/-- **Two names in lower case are the same exactly when their bytes are**, for names of bytes below 256. -/
theorem lowCodes_inj {a b : String} (ha : ∀ c ∈ (ArticleProg.lowerS a).toList, c.toNat < 256)
    (hb : ∀ c ∈ (ArticleProg.lowerS b).toList, c.toNat < 256) :
    lowCodes a = lowCodes b ↔ ArticleProg.lowerS a = ArticleProg.lowerS b := by
  constructor
  · intro h
    simp only [lowCodes, ArticleProg.codes, List.map_map] at h
    exact String.toList_inj.1 (map_ofNat_inj _ _ ha hb h)
  · intro h; simp only [lowCodes, h]

theorem esP_mem {t : String} (h : t ∈ esP) : t ∈ allNames := by
  rcases foldl_sub allNames [] t h with h | h
  · nomatch h
  · exact h

theorem class_named_of {es : List String} (hsub : ∀ t ∈ es, t ∈ allNames) {name : Bytes} {k : Nat}
    (hk : k < es.length) (hc : DN.News.ArticleRun.classOf es name = k) {nm : String} (hn : nm ∈ allNames) :
    ArticleSpec.named name nm = (ArticleProg.lowerS nm == ArticleProg.lowerS es[k]) := by
  have hf : es.findIdx? (entryIs · name) = some k := by
    unfold DN.News.ArticleRun.classOf at hc
    cases h : es.findIdx? (entryIs · name) with
    | none => rw [h, Option.getD_none] at hc; omega
    | some i => rw [h, Option.getD_some] at hc; rw [hc]
  obtain ⟨hk2, he, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
  have hm : es[k] ∈ allNames := hsub _ (List.getElem_mem _)
  unfold entryIs at he
  have he' := beq_iff_eq.1 he
  unfold ArticleSpec.named ArticleSpec.sameName
  rw [← names_ascii nm hn, he']
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff_eq, lowCodes_inj (names_small _ hm) (names_small _ hn)]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **A field of entry `k`** has a name the rules read exactly when that name is the entry's, without case. -/
theorem class_named {name : Bytes} {k : Nat} (hk : k < esP.length) (hc : DN.News.ArticleRun.classOf esP name = k)
    {nm : String} (hn : nm ∈ allNames) :
    ArticleSpec.named name nm = (ArticleProg.lowerS nm == ArticleProg.lowerS esP[k]) :=
  class_named_of (fun _ => esP_mem) hk hc hn

/-- **A field of no entry** is named none of the names the rules read. -/
theorem class_none {name : Bytes} (hc : DN.News.ArticleRun.classOf esP name = esP.length) {nm : String}
    (hn : nm ∈ allNames) :
    ArticleSpec.named name nm = false := by
  have hnone : ∀ j (hj : j < esP.length), entryIs esP[j] name = false := fun j hj => by
    unfold DN.News.ArticleRun.classOf at hc
    cases h : esP.findIdx? (entryIs · name) with
    | none => exact List.findIdx?_eq_none_iff.1 h _ (List.getElem_mem _)
    | some i =>
      rw [h, Option.getD_some] at hc
      obtain ⟨hi, -, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
      omega
  cases hb : ArticleSpec.named name nm with
  | false => rfl
  | true =>
    obtain ⟨t, ht, e⟩ := foldl_cover allNames [] nm (by simpa using hn)
    rw [← esP_eq] at ht
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    have := hnone j hj
    unfold entryIs at this
    unfold ArticleSpec.named ArticleSpec.sameName at hb
    rw [← names_ascii nm hn, ← (lowCodes_inj (names_small _ (esP_mem ht)) (names_small _ hn)).2 e] at hb
    rw [hb] at this
    nomatch this

/-! ## The premises can hold -/

theorem tabW_witness : TabW [] 0 (ArticleProg.xNameT []) := .inl rfl

/-- The area of the one entry `a`: its length, flags, rule and byte, no entry's rule, every other word 0. -/
def wTabMem : Word → Word :=
  upd (upd (upd (upd (upd (fun _ => 0) (at_ 0 (ArticleProg.xNameT ["a"] + 8)) 1)
    (at_ 0 (ArticleProg.xFlags ["a"])) (BitVec.ofNat 64 (ArticleProg.flagsOf ArticleSpec.spec "a")))
    (at_ 0 (ArticleProg.xRuleT ["a"])) (BitVec.ofNat 64 (ArticleProg.ruleOfName "a")))
    (at_ 0 (ArticleProg.xRuleT ["a"] + 8)) (BitVec.ofNat 64 AbnfRules.optionalField))
    (at_ 0 (ArticleProg.xNameBytes ["a"])) 97

theorem kindsAt_witness : KindsAt ArticleSpec.spec ["a"] 0 wTabMem := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay ["a"]
  have hl : (["a"] : List String).length = 1 := rfl
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
  · obtain rfl : k = 0 := by omega
    rw [Nat.mul_zero, Nat.add_zero, wTabMem, upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]
    rfl
  · obtain rfl : k = 0 := by omega
    rw [Nat.mul_zero, Nat.add_zero, wTabMem, upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]
    rfl
  · rw [hl, wTabMem, upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega))]
  · rw [hl, wTabMem, upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]

theorem entryAt_witness : EntryAt ArticleSpec.spec ["a"] 0 (fun _ => true) false wTabMem "a" 0 0 := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay ["a"]
  have hl : (["a"] : List String).length = 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · rw [Nat.mul_zero, Nat.add_zero, wTabMem, upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega))]
    rfl
  · rw [Nat.mul_zero, Nat.add_zero, wTabMem, upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]
    rfl
  · rw [Nat.mul_zero, Nat.add_zero, wTabMem, upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]
  · rw [Nat.mul_zero, Nat.add_zero, wTabMem, upd_ne _ (at40 (by omega) (by omega) (by omega)),
      upd_ne _ (at40 (by omega) (by omega) (by omega)), upd_eq]
  · obtain rfl : i = 0 := by have : "a".length = 1 := rfl; omega
    decide +kernel

end DN.News.ArticleTables
