-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionRun
import DN.News.CrcCode
import DN.News.SipHashCode
import DN.Compiler.Block

/-!
# DN.Server.SessionHash

The session's CRC-32C table and SipHash, proven as the session has them. `crcTable` builds the table `CrcCode` proves
(`crcTable_run`); `idHash` gives back a Message-ID's cell under the key (`idHash_run`). Both change no other word, and
the analysed heap holds their words (`covers_tableRoom`, `covers_ret`).
-/

namespace DN.Server.SessionHash

open DN.Compiler DN.Compiler.Wp DN.Compiler.WpRet DN.Compiler.Analyzer DN.Server DN.Server.SessionLayout
  DN.Server.SessionRun DN.News

variable {σ : Type}

/-! ## The CRC-32C's table -/

/-- Where the session keeps the table: in its words, at `ownCrc`. -/
def tableAt (b : Word) : Word := b + BitVec.ofNat 64 (ownOff + ownCrc)

/-- The 256 words from `t` are addressable. -/
def TableRoom (dm : Word → Bool) (t : Word) : Prop :=
  ∀ j, j < 256 → dm (t + BitVec.ofNat 64 (j * 8)) = true

/-- …and hold the table. -/
def TableIn (m : Word → Word) (t : Word) : Prop :=
  ∀ j, j < 256 → m (t + BitVec.ofNat 64 (j * 8)) = CrcCode.w32 (CrcCode.table (UInt32.ofNat j))

/-- A word that is not one of the table's from `t`. -/
def Outside (t a : Word) : Prop := ∀ j, j < 256 → a ≠ t + BitVec.ofNat 64 (j * 8)

/-- After `k` words of the fill: the memory outside the table as it was, `m0`. -/
def FrameW (t : Word) (m0 : Word → Word) (k : Nat) (s : PancakeState σ) : Prop :=
  s.locals "t" = some t ∧ s.locals "i" = some (BitVec.ofNat 64 k) ∧ TableRoom s.memaddrs t ∧
    ∀ a, Outside t a → s.memory a = m0 a

/-- The fill's loop, kept: some first words written, `c` bound, the rest of the memory alone. -/
def FrameI (t : Word) (m0 : Word → Word) (s : PancakeState σ) : Prop :=
  ∃ k, k ≤ 256 ∧ FrameW t m0 k s ∧ ∃ c, s.locals "c" = some c

/-- The fill, its loop carrying `FrameI`: the same program as `CrcCode.fillA`. -/
def fillF (t : Word) (m0 : Word → Word) : AProg σ :=
  .seq (.assign "i" (.c 0)) <|
    .while_ (FrameI t m0) (.cmp .less (.var "i") (.c 256))
      (.seq (.assign "c" (.var "i")) <| CrcCode.nShifts 8 <|
        .seq (.store (.op .add (.var "t") (.mul (.var "i") (.c 8))) (.var "c"))
          (.assign "i" (.op .add (.var "i") (.c 1))))

theorem fillF_erase (t : Word) (m0 : Word → Word) :
    (fillF (σ := σ) t m0).erase = (CrcCode.fillA (σ := σ) t).erase := rfl

theorem frameW_set {t : Word} {m0 : Word → Word} {k : Nat} {s : PancakeState σ}
    (h : FrameW t m0 k s) {x : String} (ht : x ≠ "t") (hi : x ≠ "i") (w : Value) :
    FrameW t m0 k { s with locals := setLocal s.locals x w } :=
  ⟨by simp [setLocal, Ne.symm ht, h.1], by simp [setLocal, Ne.symm hi, h.2.1], h.2.2⟩

theorem shifts_frame {t : Word} {m0 : Word → Word} {k : Nat} {rest : AProg σ} {Q : Assn σ} :
    ∀ (n : Nat) (s : PancakeState σ), FrameW t m0 k s → (∃ c, s.locals "c" = some c) →
      (∀ s', FrameW t m0 k s' → (∃ c, s'.locals "c" = some c) → wp rest Q s') →
      wp (CrcCode.nShifts n rest) Q s
  | 0, s, hw, hc, hr => hr s hw hc
  | n + 1, s, hw, ⟨c, hc⟩, hr => by
    have he : ∃ w, eval s CrcCode.shiftE = some w := by simp [CrcCode.shiftE, eval, hc, PancakeExp.c]
    obtain ⟨w, hw'⟩ := he
    exact wp_seq (wp_assign hw' hc (Q := fun s' => FrameW t m0 k s' ∧ ∃ c, s'.locals "c" = some c)
      ⟨frameW_set hw (by decide) (by decide) _, w, by simp [setLocal]⟩)
      fun s' ⟨h1, h2⟩ => shifts_frame n s' h1 h2 hr

theorem frame_step (t : Word) (m0 : Word → Word) (k : Nat) (hk : k < 256) (s : PancakeState σ)
    (hw : FrameW t m0 k s) (hc : ∃ c, s.locals "c" = some c) :
    wp (.seq (.assign "c" (.var "i")) <| CrcCode.nShifts 8 <|
        .seq (.store (.op .add (.var "t") (.mul (.var "i") (.c 8))) (.var "c"))
          (.assign "i" (.op .add (.var "i") (.c 1)))) (FrameI (σ := σ) t m0) s := by
  obtain ⟨c, hc⟩ := hc
  refine wp_seq (wp_assign (val := BitVec.ofNat 64 k) (by simp [eval, hw.2.1]) hc
    (Q := fun s' => FrameW t m0 k s' ∧ ∃ c, s'.locals "c" = some c)
    ⟨frameW_set hw (by decide) (by decide) _, BitVec.ofNat 64 k, by simp [setLocal]⟩) fun s1 ⟨hw1, hc1⟩ => ?_
  refine shifts_frame 8 s1 hw1 hc1 fun s2 hw2 ⟨c2, hc2⟩ => ?_
  obtain ⟨ht2, hi2, hdm2, hm2⟩ := hw2
  have haddr : eval s2 (.op .add (.var "t") (.mul (.var "i") (.c 8))) =
      some (t + BitVec.ofNat 64 (k * 8)) := by
    simp only [eval, ht2, hi2, PancakeExp.c, Option.some.injEq]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul] <;> omega
  refine wp_seq (wp_store (val := c2)
    (m := fun x => if x = t + BitVec.ofNat 64 (k * 8) then c2 else s2.memory x) haddr
    (by simp [eval, hc2]) (by simp [memStoreWord, hdm2 k hk])
    (Q := fun s3 => FrameW t m0 k s3 ∧ ∃ c, s3.locals "c" = some c)
    ⟨⟨ht2, hi2, hdm2, fun a ha => ?_⟩, c2, hc2⟩) fun s3 ⟨⟨ht3, hi3, hdm3, hm3⟩, c3, hc3⟩ => ?_
  · simp only [if_neg (ha k hk)]
    exact hm2 a ha
  · refine wp_assign (val := BitVec.ofNat 64 (k + 1))
      (by simp [eval, hi3, PancakeExp.c, BitVec.ofNat_add]) hi3
      ⟨k + 1, by omega, ⟨by simp [setLocal, ht3], by simp [setLocal], hdm3, hm3⟩, c3, ?_⟩
    simp [setLocal, hc3]

theorem frame_vc (t : Word) (m0 : Word → Word) :
    vc (fillF (σ := σ) t m0) (fun s => ∀ a, Outside t a → s.memory a = m0 a) := by
  refine ⟨trivial, fun s k h => h, by simp only [CrcCode.nShifts, vc_seq, vc_assign, vc_store, and_self],
    fun s ⟨k, hk, hw, hc⟩ => ?_⟩
  simp only [eval, hw.2.1, PancakeExp.c,
    WpBytes.signedLt_small (by omega : k < 2 ^ 63) (by decide : 256 < 2 ^ 63)]
  by_cases hlt : k < 256
  · simp only [hlt, decide_true, if_true, show ((1 : Word) = 0) = False by decide, if_false]
    exact frame_step t m0 k hlt s hw hc
  · simp only [hlt, decide_false, Bool.false_eq_true, if_false, if_true]
    exact hw.2.2.2

/-- **The fill writes only the table**: every other word keeps what it held. -/
theorem fill_frame (o : Oracle σ) (t : Word) (m0 : Word → Word) :
    Safe.Safe o (fun s => CrcCode.FillGiven t s ∧ s.memory = m0) (CrcCode.fillA (σ := σ) t).erase
      (fun s => ∀ a, Outside t a → s.memory a = m0 a) := by
  rw [← fillF_erase t m0]
  refine Safe.conseq (wp_sound o _ _ (fun _ _ h => h) (frame_vc t m0)) (fun s ⟨h, hm⟩ => ?_)
    (fun _ h => h)
  obtain ⟨ht, hdm, ⟨vi, hi⟩, ⟨vc, hc⟩⟩ := h
  simp only [fillF, wp, eval, PancakeExp.c, hi]
  exact ⟨0, by omega, ⟨by simp [setLocal, ht], by simp [setLocal], hdm, fun a _ => by simp [hm]⟩, vc,
    by simp [setLocal, hc]⟩

/-- The table's statements, then the return. -/
theorem table_tail (o : Oracle σ) (t : Word) :
    ∃ c, Lower.lowerStmtsFold (CrcProg.fillSrc ++ [SessionStore.done0]) = some c ∧
      ∀ s, PancakeSem o c s = PancakeSem o (.seq (CrcCode.fillA (σ := σ) t).erase (.ret (.const 0))) s :=
  Block.fold_append o _ _ (by simp [CrcProg.fillSrc]) (by simp) (by decide)
    (CrcCode.fill_lowering t) rfl

/-- **The session's `crcTable` builds the CRC-32C's table** in the session's addressable words. It leaves every other
word as it was and returns zero. -/
theorem crcTable_run (o : Oracle σ) (b : Word) (m0 : Word → Word) {body : PancakeProg}
    (hb : Lower.lower SessionStore.crcTable = some body) :
    SafeR o (fun s => s.baseAddr = b ∧ TableRoom s.memaddrs (tableAt b) ∧ s.memory = m0) body
      (fun v m => v = 0 ∧ TableIn m (tableAt b) ∧ ∀ a, Outside (tableAt b) a → m a = m0 a)
      (fun _ => False) := by
  obtain ⟨c, hc, hrun⟩ := table_tail o (tableAt b)
  have e : Lower.lower SessionStore.crcTable =
      (Lower.lowerStmtsFold (CrcProg.fillSrc ++ [SessionStore.done0])).map fun c =>
        .dec "t" (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownCrc))))
          (.dec "i" (.const 0) (.dec "c" (.const 0) c)) := rfl
  rw [e, hc] at hb
  cases hb
  have hfill := both (Safe.conseq (CrcCode.fill_safe o (tableAt b)) (fun s h => h.1)
    (fun _ h => h)) (fill_frame o (tableAt b) m0)
  have hc' : SafeR o (fun s => CrcCode.FillGiven (tableAt b) s ∧ s.memory = m0) c
      (fun v m => v = 0 ∧ TableIn m (tableAt b) ∧ ∀ a, Outside (tableAt b) a → m a = m0 a)
      (fun _ => False) := by
    intro s hs
    rw [hrun]
    refine seq (ofSafe _ rfl hfill) (ret fun s h => ⟨0, rfl, rfl, fun j hj => (h.1.2 j hj).2, h.2⟩)
      (fun _ _ h => h) s hs
  refine dec (P' := fun s => (s.locals "t" = some (tableAt b) ∧ TableRoom s.memaddrs (tableAt b)) ∧
    s.memory = m0) (Q' := fun _ => False) (fun s hs => ⟨tableAt b, ?_, ?_⟩) ?_ (fun _ _ _ h => h.elim)
  · simp [eval, hs.1, tableAt]
  · exact ⟨⟨by simp [setLocal], hs.2.1⟩, hs.2.2⟩
  refine dec (P' := fun s => ((s.locals "t" = some (tableAt b) ∧ TableRoom s.memaddrs (tableAt b)) ∧
    s.memory = m0) ∧ ∃ w, s.locals "i" = some w) (Q' := fun _ => False)
    (fun s hs => ⟨0, rfl, ?_⟩) ?_ (fun _ _ _ h => h.elim)
  · exact ⟨⟨⟨by simp [setLocal, hs.1.1], hs.1.2⟩, hs.2⟩, 0, by simp [setLocal]⟩
  refine dec (P' := fun s => CrcCode.FillGiven (tableAt b) s ∧ s.memory = m0) (Q' := fun _ => False)
    (fun s hs => ⟨0, rfl, ?_⟩) hc' (fun _ _ _ h => h.elim)
  obtain ⟨⟨⟨ht, hr⟩, hm⟩, w, hi⟩ := hs
  exact ⟨⟨by simp [setLocal, ht], hr, ⟨w, by simp [setLocal, hi]⟩, 0, by simp [setLocal]⟩, hm⟩

/-! ## The cell of a Message-ID -/

/-- Where the index's key, the Message-ID and the return word lie: in the session's words. -/
def keyAt (b : Word) : Word := b + BitVec.ofNat 64 (ownOff + ownIndexKey)
def idAt (b : Word) : Word := b + BitVec.ofNat 64 (ownOff + ownId)
def retAt (b : Word) : Word := b + BitVec.ofNat 64 (ownOff + ownRet)

/-- The cell a Message-ID hashes to: the tag's low bits, as many as the index has cells. -/
def cellOf (key msg : SipHash.Bytes) : Word :=
  (SipHash.tag key msg).toBitVec &&& BitVec.ofNat 64 (indexCells - 1)

/-- What `idHash` asks: the Message-ID's length, at most 250, in `n`. The index's key and the Message-ID in the
session's words, the return word addressable. -/
def IdPre (b : Word) (key msg : SipHash.Bytes) (s : PancakeState σ) : Prop :=
  s.baseAddr = b ∧ s.locals "n" = some (BitVec.ofNat 64 msg.length) ∧ msg.length ≤ 250 ∧
    readByteArray s.memory s.memaddrs s.be (keyAt b) 16 = some key ∧
    readByteArray s.memory s.memaddrs s.be (idAt b) msg.length = some msg ∧
    s.memaddrs (retAt b) = true

theorem idPre_set {b : Word} {key msg : SipHash.Bytes} {s : PancakeState σ} (h : IdPre b key msg s)
    {y : String} (hy : y ≠ "n") (w : Value) : IdPre b key msg { s with locals := setLocal s.locals y w } :=
  ⟨h.1, by simp [setLocal, Ne.symm hy, h.2.1], h.2.2⟩

/-- The locals `idHash` declares from zero, those of the hash. -/
def hashLocals : List String := ["r", "m", "v0", "v1", "v2", "v3", "off", "j"]

/-- The hash's statements, then the cell into the return word and the return. -/
theorem hash_tail (o : Oracle σ) (b : Word) (key msg : SipHash.Bytes) :
    ∃ c, Lower.lowerStmtsFold (SipProg.sipSrc ++
        SessionStore.give (Syntax.eAnd (Syntax.v "r") (Syntax.n (indexCells - 1)))) = some c ∧
      ∀ s, PancakeSem o c s = PancakeSem o (.seq (SipHashCode.sipA (σ := σ) (keyAt b) (idAt b) key msg).erase
        (.seq (.store (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownRet))))
            (.op .and_ (.var "r") (.const (BitVec.ofNat 64 (indexCells - 1)))))
          (.ret (.const 0)))) s :=
  Block.fold_append o _ _ (by simp [SipProg.sipSrc]) (by simp [SessionStore.give]) (by decide)
    (SipHashCode.sip_lowering _ _ _ _) rfl

/-- `idHash` lowers to the check of `n`, the key's and Message-ID's places, the hash's locals from zero, and its
statements. -/
theorem idHash_lower {c : PancakeProg} (hc : Lower.lowerStmtsFold (SipProg.sipSrc ++
      SessionStore.give (Syntax.eAnd (Syntax.v "r") (Syntax.n (indexCells - 1)))) = some c) :
    Lower.lower SessionStore.idHash = some (.seq (keptG (.var "n") 250)
      (.dec "k" (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownIndexKey))))
        (.dec "p" (.op .add .base (.const (BitVec.ofNat 64 (ownOff + ownId)))) (zeros hashLocals c)))) := by
  have hne : SipProg.sipSrc ++ SessionStore.give (Syntax.eAnd (Syntax.v "r") (Syntax.n (indexCells - 1)))
      ≠ [] := by simp [SessionStore.give]
  have hz := Block.fold_zeros hashLocals hne hc
  have hp := Block.fold_dec (x := "p") (e := SessionStore.at_ (ownOff + ownId)) rfl
    (by simp [hashLocals]) hz
  have hk := Block.fold_dec (x := "k") (e := SessionStore.at_ (ownOff + ownIndexKey)) rfl
    (by simp) hp
  have hl := Block.fold_cons (x := SessionStore.keptIn (Syntax.v "n") 250) (a := keptG (.var "n") 250)
    (keptIn_lower rfl 250) rfl (by simp) hk
  have e : Lower.lower SessionStore.idHash = Lower.lowerStmtsFold
      (SessionStore.keptIn (Syntax.v "n") 250 :: .dec "k" (SessionStore.at_ (ownOff + ownIndexKey)) ::
        .dec "p" (SessionStore.at_ (ownOff + ownId)) ::
        (hashLocals.map (fun x => Syntax.PStmt.dec x (Syntax.n 0)) ++ (SipProg.sipSrc ++
          SessionStore.give (Syntax.eAnd (Syntax.v "r") (Syntax.n (indexCells - 1)))))) := by
    simp only [Lower.lower, SessionStore.idHash, hashLocals, List.append_assoc, List.cons_append,
      List.nil_append]
  rw [e]
  exact hl

/-- **The session's `idHash` gives back the cell a Message-ID hashes to** under the index's key. It puts it in the
return word, changes no other word, and returns zero. -/
theorem idHash_run (o : Oracle σ) (b : Word) (key msg : SipHash.Bytes) (m0 : Word → Word)
    {body : PancakeProg} (hb : Lower.lower SessionStore.idHash = some body) :
    SafeR o (fun s => IdPre b key msg s ∧ s.memory = m0) body
      (fun v m => v = 0 ∧ m (retAt b) = cellOf key msg ∧ ∀ a, a ≠ retAt b → m a = m0 a)
      (fun _ => False) := by
  obtain ⟨c, hc, hrun⟩ := hash_tail o b key msg
  rw [idHash_lower hc] at hb
  cases hb
  refine seq (keptG_pass o _ (by decide) fun s hs => ⟨msg.length, hs.1.2.2.1, hs.1.2.1⟩) ?_
    (fun s k h => h)
  refine dec (P' := fun s => (IdPre b key msg s ∧ s.memory = m0) ∧ s.locals "k" = some (keyAt b))
    (Q' := fun _ => False) (fun s hs => ⟨keyAt b, by simp [eval, hs.1.1, keyAt], ?_⟩) ?_
    (fun _ _ _ h => h.elim)
  · exact ⟨⟨idPre_set hs.1 (by decide) _, hs.2⟩, by simp [setLocal]⟩
  refine dec (P' := fun s => ((IdPre b key msg s ∧ s.memory = m0) ∧ s.locals "k" = some (keyAt b)) ∧
    s.locals "p" = some (idAt b)) (Q' := fun _ => False)
    (fun s hs => ⟨idAt b, by simp [eval, hs.1.1.1, idAt], ?_⟩) ?_ (fun _ _ _ h => h.elim)
  · exact ⟨⟨⟨idPre_set hs.1.1 (by decide) _, hs.1.2⟩, by simp [setLocal, hs.2]⟩, by simp [setLocal]⟩
  have hnot : ∀ y ∈ hashLocals, y ≠ "n" ∧ y ≠ "k" ∧ y ≠ "p" := by decide
  refine zeros_run hashLocals (fun s y w hs hy => ?_) ?_
  · obtain ⟨hn, hk, hp⟩ := hnot y hy
    exact ⟨⟨⟨idPre_set hs.1.1.1 hn w, hs.1.1.2⟩, by simp [setLocal, Ne.symm hk, hs.1.2]⟩,
      by simp [setLocal, Ne.symm hp, hs.2]⟩
  intro s ⟨⟨⟨⟨hpre, hm⟩, hk⟩, hp⟩, hbd⟩
  rw [hrun]
  have hlen : msg.length < 2 ^ 62 := Nat.lt_of_le_of_lt hpre.2.2.1 (by decide)
  have hwork : ∀ y ∈ SipHashCode.work, y ∈ hashLocals := by decide
  have hsip := keepsMemory (keeps (SipHashCode.sip_safe o (keyAt b) (idAt b) key msg hlen)
    s.memaddrs b) rfl m0
  have hpre' : SipHashCode.SipPre (keyAt b) (idAt b) key msg s :=
    ⟨⟨hk, hp, hpre.2.1, hbd "r" (by simp [hashLocals]), hpre.2.2.2.1, hpre.2.2.2.2.1⟩,
      fun y hy => hbd y (hwork y hy)⟩
  refine seq (ofSafe _ rfl hsip) (seq (M := fun t => t.memory (retAt b) = cellOf key msg ∧
      ∀ a, a ≠ retAt b → t.memory a = m0 a)
    (store fun t ht => ?_) (ret fun t ht => ⟨0, rfl, rfl, ht⟩) (fun _ _ h => h)) (fun _ _ h => h)
    s ⟨⟨hpre', rfl, hpre.1⟩, hm⟩
  obtain ⟨⟨hr, hdm, hbase⟩, htm⟩ := ht
  refine ⟨retAt b, cellOf key msg, fun k => if k = retAt b then cellOf key msg else t.memory k,
    by simp [eval, hbase, retAt], by simp [eval, hr, cellOf], ?_, by simp, fun a ha => by simp [ha, htm]⟩
  simp [memStoreWord, hdm, hpre.2.2.2.2.2]

/-! ## In the session's code -/

theorem crcTable_mem : SessionStore.crcTable ∈ Session.functions :=
  List.mem_append_left _ (List.mem_append_right _ (by unfold SessionStore.functions; simp))

theorem idHash_mem : SessionStore.idHash ∈ Session.functions :=
  List.mem_append_left _ (List.mem_append_right _ (by unfold SessionStore.functions; simp))

/-- **In the session's code, `crcTable` is the function `crcTable_run` proves.** -/
theorem crcTable_code {s : PancakeState σ}
    (hcode : ∀ f ps body k, (f, ps, body, k) ∈ SessionCert.fnsC → s.code f = some (ps, body)) :
    ∃ body, Lower.lower SessionStore.crcTable = some body ∧ s.code "crcTable" = some ([], body) := by
  obtain ⟨c, hc, -⟩ := table_tail (σ := σ) Oracle.idle 0
  have hl : ∃ body, Lower.lower SessionStore.crcTable = some body := ⟨_, by
    show Lower.lowerStmtsFold (_ :: _ :: _ :: (CrcProg.fillSrc ++ [SessionStore.done0])) = _
    rw [Block.fold_dec rfl (by simp) (Block.fold_dec rfl (by simp) (Block.fold_dec rfl (by simp) hc))]⟩
  obtain ⟨body, hb⟩ := hl
  exact ⟨body, hb, by simpa [hb] using in_code crcTable_mem hcode⟩

/-- **In the session's code, `idHash` is the function `idHash_run` proves.** -/
theorem idHash_code {s : PancakeState σ}
    (hcode : ∀ f ps body k, (f, ps, body, k) ∈ SessionCert.fnsC → s.code f = some (ps, body)) :
    ∃ body, Lower.lower SessionStore.idHash = some body ∧ s.code "idHash" = some (["n"], body) := by
  obtain ⟨c, hc, -⟩ := hash_tail (σ := σ) Oracle.idle 0 [] []
  have hb := idHash_lower hc
  exact ⟨_, hb, by simpa [hb] using in_code idHash_mem hcode⟩

/-! ## The premises can hold -/

/-- Where the session's words lie in its layout, computed once. -/
theorem layout :
    floor ≤ ownOff + ownCrc ∧ ownOff + ownCrc + 255 * 8 < SessionLayout.size ∧
      (ownOff + ownCrc) % 8 = 0 ∧ floor ≤ ownOff + ownRet ∧ ownOff + ownRet < SessionLayout.size ∧
      (ownOff + ownRet) % 8 = 0 ∧ floor ≤ ownOff + ownIndexKey ∧
      ownOff + ownIndexKey + 16 ≤ SessionLayout.size ∧ floor ≤ ownOff + ownId ∧
      ownOff + ownId + 250 ≤ SessionLayout.size := by
  decide +kernel

/-- The heap the safety analysis covers holds the table's words… -/
theorem covers_tableRoom {dm : Word → Bool} {b : Word} (h : Covers SessionLayout.size dm b) :
    TableRoom dm (tableAt b) := by
  intro j hj
  obtain ⟨h1, h2, h3, -⟩ := layout
  have := h.2 (ownOff + ownCrc + j * 8) (by omega) (by omega) (by omega)
  simpa [tableAt, BitVec.ofNat_add, BitVec.add_assoc] using this

/-- …the return word… -/
theorem covers_ret {dm : Word → Bool} {b : Word} (h : Covers SessionLayout.size dm b) :
    dm (retAt b) = true := by
  obtain ⟨-, -, -, h1, h2, h3, -⟩ := layout
  exact h.2 _ h1 h2 h3

/-- …and the octets of the index's key and of a Message-ID of at most 250. So `idHash`'s premise holds of whatever they
are. -/
theorem covers_reads {s : PancakeState σ} (h : Covers SessionLayout.size s.memaddrs s.baseAddr)
    (len : Nat) (hlen : len ≤ 250) :
    (∃ key, readByteArray s.memory s.memaddrs s.be (keyAt s.baseAddr) 16 = some key ∧
      key.length = 16) ∧
    ∃ msg, readByteArray s.memory s.memaddrs s.be (idAt s.baseAddr) len = some msg ∧
      msg.length = len := by
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4⟩ := layout
  refine ⟨SessionRun.readByteArray_some _ 16 fun j hj => ?_,
    SessionRun.readByteArray_some _ len fun j hj => ?_⟩
  · have := h.1 (ownOff + ownIndexKey + j) (Nat.le_trans h1 (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) h2)
    simpa [keyAt, BitVec.ofNat_add, BitVec.add_assoc] using this
  · have := h.1 (ownOff + ownId + j) (Nat.le_trans h3 (Nat.le_add_right _ _))
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hj hlen) _) h4)
    simpa [idAt, BitVec.ofNat_add, BitVec.add_assoc] using this

/-- The fill's invariant can hold: none written, the memory as it was. -/
theorem frameW_witness :
    FrameW (σ := Unit) 0 (fun _ => 0) 0
      { bareState () with locals := setLocal (setLocal (fun _ => none) "t" 0) "i" 0 } :=
  ⟨by simp [setLocal], by simp [setLocal], fun _ _ => rfl, fun _ _ => rfl⟩

/-- Every word addressable: the table's room. -/
theorem tableRoom_witness (b : Word) : TableRoom (fun _ => true) (tableAt b) := fun _ _ => rfl

/-- A key of zeros and a Message-ID of three octets, in a memory of zeros all addressable. -/
theorem idPre_witness :
    IdPre (σ := Unit) 0 (List.replicate 16 0) (List.replicate 3 0)
      { bareState () with locals := setLocal (fun _ => none) "n" 3 } :=
  ⟨rfl, by simp [setLocal], by decide, by decide, by decide, rfl⟩

end DN.Server.SessionHash
