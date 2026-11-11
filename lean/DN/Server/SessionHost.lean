-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Server.SessionStoreAt
import DN.News.FunRun
import DN.News.ScanFrame

/-!
# DN.Server.SessionHost

What the session and its host hand each other, as `SessionSpec` has it. `dn_next` writes only its array
(`fetch_frag`), whose words hold a batch: its clocks, events (`EventAt`) and completions (`DoneAt`).
-/

namespace DN.Server.SessionHost

open DN.Compiler DN.Compiler.Frag DN.News.FunRun DN.Server.SessionLayout DN.News.SessionSpec
open DN.News.FramerCode (Chunk bw)
open DN.Server.SessionState (NumW)
open DN.Server.SessionStoreAt (WordN)
open DN.News.PostSpec (Done)

variable {σ : Type}

/-- Word `k` of the `dn_next` array. -/
def nextW (b : Word) (k : Nat) : Word := b + BitVec.ofNat 64 (nextOff + k)
/-- Word `k` of the batch's event `e`. -/
def evW (b : Word) (e k : Nat) : Word := nextW b (nextEvents + e * eventSlot + k)
/-- Word `k` of the batch's completion slot `j`. -/
def doneW (b : Word) (j k : Nat) : Word := nextW b (nextDone + j * doneSlot + k)

/-- An event's index, as its slot codes it. -/
def evIdx : Event → Nat
  | .opened i .. | .received i .. | .writable i _ | .inputEnded i _ | .closed i _ | .verified i .. => i

/-- An event's generation. -/
def evGen : Event → Nat
  | .opened _ g .. | .received _ g _ | .writable _ g | .inputEnded _ g | .closed _ g | .verified _ g _ => g

/-- An event's kind, as its slot codes it. -/
def evKind : Event → Nat
  | .opened .. => SessionLayout.opened
  | .received .. => SessionLayout.received
  | .writable .. => SessionLayout.writable
  | .inputEnded .. => SessionLayout.inputEnded
  | .closed .. => SessionLayout.closed
  | .verified .. => SessionLayout.verified

/-- A flag word: set unless zero. -/
def flag (w : Word) : Bool := w != 0

/-- **Slot `e` of the batch holds `ev`.** Of an index past the table the specification reads nothing else
(`checkIndex`). Of the bytes received past a chunk, only their count (`tooLong`). -/
structure EventAt (b : Word) (e : Nat) (ev : Event) (s : PancakeState σ) : Prop where
  idx : (s.memory (evW b e eventIdx)).toNat = evIdx ev
  kind : evIdx ev < SessionLayout.conns → s.memory (evW b e eventKind) = BitVec.ofNat 64 (evKind ev)
  gen : evIdx ev < SessionLayout.conns → (s.memory (evW b e eventGen)).toNat = evGen ev
  body : evIdx ev < SessionLayout.conns → match ev with
    | .opened _ _ p lg t => p = flag (s.memory (evW b e eventPost)) ∧ lg = flag (s.memory (evW b e eventLogins)) ∧
      t = flag (s.memory (evW b e eventTls))
    | .received _ _ bs => bs.length = (s.memory (evW b e eventLen)).toNat ∧
      (bs.length ≤ data → Chunk s (evW b e eventHead) bs)
    | .verified _ _ ok => ok = flag (s.memory (evW b e eventPost))
    | _ => True

/-- The result words of completion slot `j`, as many as its operations done, up to a job's. -/
def resultsOf (b : Word) (j : Nat) (s : PancakeState σ) : List (Nat × Nat) :=
  (List.range (min (s.memory (doneW b j doneOps)).toNat jobOps)).map fun k =>
    ((s.memory (doneW b j (doneResults + 16 * k))).toNat,
      (s.memory (doneW b j (doneResults + 16 * k + 8))).toNat)

/-- **Completion slot `j` holds `d`.** The octets read are as many as its first result word gives, within a job's.
Past a job's, none: the specification's `badDone`. -/
structure DoneAt (b : Word) (j : Nat) (d : Done) (s : PancakeState σ) : Prop where
  slot : d.slot = j
  gen : (s.memory (doneW b j doneGen)).toNat = d.gen
  ok : (s.memory (doneW b j doneOps)).toNat = d.ok
  results : d.results = resultsOf b j s
  data : match d.results with
    | (got, _) :: _ =>
      if got ≤ jobData then d.data.length = got ∧ Chunk s (doneW b j doneHead) d.data else d.data = []
    | [] => d.data = []

/-- **The batch's clocks, events and completions.** The specification takes as many events as the count says. It
takes the completions of the slots holding one, in order. -/
structure BatchAt (b : Word) (now wall : Nat) (events : List Event) (slots : List (Option Done))
    (s : PancakeState σ) : Prop where
  clock : (s.memory (nextW b nextClock)).toNat = now
  wall : (s.memory (nextW b nextWall)).toNat = wall
  count : (s.memory (nextW b nextCount)).toNat = events.length
  events : events.length ≤ SessionLayout.batch → ∀ e (h : e < events.length), EventAt b e events[e] s
  len : slots.length = jobs
  dones : ∀ j, j < jobs → match slots.getD j none with
    | none => s.memory (doneW b j doneKind) = 0
    | some d => s.memory (doneW b j doneKind) ≠ 0 ∧ DoneAt b j d s

/-! ## The layout -/

/-- The `dn_next` array lies past the heap's header and within the session's words. -/
theorem next_in {x : Nat} (hx : x < nextLen) : Analyzer.floor ≤ nextOff + x ∧ nextOff + x < SessionLayout.size := by
  obtain ⟨-, -, h2, h3, h4, -, h6, -⟩ := areas_disjoint
  have h3' : emitOff ≤ ownOff := Nat.le_trans (Nat.le_add_right _ _) h3
  have h4' : ownOff ≤ tableOff := Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) h4
  have h6' : tableOff ≤ SessionLayout.size :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) h6
  have h0 : Analyzer.floor ≤ nextOff := by decide
  clear h3 h4 h6
  generalize SessionLayout.size = S at h6' ⊢
  generalize tableOff = T at h4' h6'
  generalize ownOff = O at h3' h4'
  generalize emitOff = M at h2 h3'
  generalize nextLen = N at h2 hx
  generalize Analyzer.floor = F at h0 ⊢
  generalize nextOff = X at h0 h2 ⊢
  omega

theorem event_le {e k : Nat} (he : e < SessionLayout.batch) (hk : k ≤ eventSlot) :
    nextEvents + e * eventSlot + k ≤ nextLen := by
  have h1 : (e + 1) * eventSlot ≤ SessionLayout.batch * eventSlot := Nat.mul_le_mul_right _ he
  have h2 : nextEvents + SessionLayout.batch * eventSlot ≤ nextLen := by
    show nextDoneCount ≤ nextLen
    unfold nextLen nextDone
    omega
  rw [Nat.succ_mul] at h1
  omega

theorem done_le {j k : Nat} (hj : j < jobs) (hk : k ≤ doneSlot) : nextDone + j * doneSlot + k ≤ nextLen := by
  have h1 : (j + 1) * doneSlot ≤ jobs * doneSlot := Nat.mul_le_mul_right _ hj
  rw [Nat.succ_mul] at h1
  unfold nextLen
  omega

/-! ## `dn_next` -/

/-- A byte of the session's words lies in an addressable word. -/
theorem byte_dom {s0 : PancakeState σ} {b : Word} (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b)
    {x : Nat} (hf : Analyzer.floor ≤ x) (j : Nat) (hj : x + j < SessionLayout.size) :
    s0.memaddrs (byteAlign (b + BitVec.ofNat 64 x + BitVec.ofNat 64 j)) = true := by
  rw [Bytes.add_ofNat]; exact hcov.1 _ (by omega) hj

/-- **An external call writes only its array**, at `X` past `@base`. Every word of the heap before or past it is
kept. The configuration word is read. -/
theorem call_frag (o : Oracle σ) {name : String} {X N : Nat} (hX0 : X % 8 = 0) (hXf : Analyzer.floor ≤ X)
    (hXN : X + N ≤ SessionLayout.size) {s0 : PancakeState σ} {b : Word} (hb0 : s0.baseAddr = b)
    (hb : b.toNat % 8 = 0)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) {l : List (String × Value)} {M : Word → Word} :
    Frag o [.ffi name [SessionStore.at_ confOff, Syntax.n confLen, SessionStore.at_ X, Syntax.n N]] (RunF s0 l (· = M))
      (fun u => ∃ M', RunF s0 l (· = M') u ∧ ∀ y, y < 2 ^ 64 → (y < X ∨ X + N ≤ y) →
        M' (b + BitVec.ofNat 64 y) = M (b + BitVec.ofNat 64 y)) := by
  have hcl : confOff + confLen ≤ SessionLayout.size := by
    have h := (next_in (x := 0) (by decide)).2
    obtain ⟨-, hc, -, -⟩ := areas_disjoint
    generalize confOff + confLen = C at hc ⊢
    generalize nextOff = Y at hc h
    omega
  have hcf : Analyzer.floor ≤ confOff := by decide
  have hS : SessionLayout.size < 2 ^ 63 := SessionAppend.size_lt
  have hX : X ≠ 0 := by have : Analyzer.floor = 64 := rfl; omega
  have hlow : Lower.lowerStmt1 (.ffi name [SessionStore.at_ confOff, Syntax.n confLen, SessionStore.at_ X,
      Syntax.n N]) = some (PancakeProg.extCall name (.op .add .base (.const (BitVec.ofNat 64 confOff)))
        (.const (BitVec.ofNat 64 confLen)) (.op .add .base (.const (BitVec.ofNat 64 X)))
        (.const (BitVec.ofNat 64 N))) := by
    simp only [Lower.lowerStmt1, SessionAppend.at_lower (show confOff ≠ 0 by decide), SessionAppend.at_lower hX,
      Syntax.n, Lower.lowerExp]
  refine frag_one hlow rfl rfl
    (fun _ _ ⟨M', h, hk⟩ => ⟨M', runF_clock _ _ _ _ _ h, hk⟩) (Safe.extCall fun s hs => ?_)
  have hbase : s.baseAddr = b := by rw [hs.1.base, hb0]
  obtain ⟨conf, hconf, -⟩ := Bytes.readByteArray_some (m := s.memory) (dm := s.memaddrs) (be := s.be)
    (b + BitVec.ofNat 64 confOff) confLen fun j hj => by
      rw [hs.1.memaddrs]; exact byte_dom hcov hcf j (by omega)
  obtain ⟨arr, harr, hal⟩ := Bytes.readByteArray_some (m := s.memory) (dm := s.memaddrs) (be := s.be)
    (b + BitVec.ofNat 64 X) N fun j hj => by
      rw [hs.1.memaddrs]; exact byte_dom hcov hXf j (by omega)
  refine ⟨b + BitVec.ofNat 64 confOff, BitVec.ofNat 64 confLen, b + BitVec.ofNat 64 X, BitVec.ofNat 64 N,
    conf, arr, by simp only [eval, hbase], rfl, by simp only [eval, hbase], rfl,
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]; exact hconf,
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact harr,
    fun ffi' bytes hl =>
      ⟨_, ⟨⟨hs.1.vals, hs.1.memaddrs, hs.1.base, hs.1.code, hs.1.be⟩, rfl⟩, fun y hy hyo => ?_⟩⟩
  show writeByteArray s.memaddrs s.be (b + BitVec.ofNat 64 X) bytes s.memory (b + BitVec.ofNat 64 y) =
    M (b + BitVec.ofNat 64 y)
  rw [Bytes.writeByteArray_keep _ _ bytes _ s.memory fun j hj => ?_, hs.2]
  rw [hl, hal] at hj
  rw [Bytes.add_ofNat, show b + BitVec.ofNat 64 (X + j) = DN.News.ScanRun.at_ b (X + j) from rfl,
    DN.News.ScanRun.align_at hb]
  have hle : (X + j) / 8 * 8 ≤ X + j := Nat.div_mul_le_self _ _
  have hge : X ≤ (X + j) / 8 * 8 := by omega
  exact DN.News.ScanRun.at_ne (by omega) hy (by omega)

/-- **`dn_next` writes only its array.** -/
theorem fetch_frag (o : Oracle σ) {s0 : PancakeState σ} {b : Word} (hb0 : s0.baseAddr = b) (hb : b.toNat % 8 = 0)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) {l : List (String × Value)} {M : Word → Word} :
    Frag o [Session.fetch] (RunF s0 l (· = M))
      (fun u => ∃ M', RunF s0 l (· = M') u ∧ ∀ y, y < 2 ^ 64 → (y < nextOff ∨ nextOff + nextLen ≤ y) →
        M' (b + BitVec.ofNat 64 y) = M (b + BitVec.ofNat 64 y)) :=
  have hn := next_in (x := nextLen - 1) (by decide)
  call_frag o offsets_aligned.2.1 (next_in (x := 0) (by decide)).1 (by omega) hb0 hb hcov

/-! ## A batch as the specification reads it -/

/-- Octets from word `k` of the `dn_next` array on, while within it, lie in addressable words. -/
theorem next_bytes {s : PancakeState σ} {b : Word} (hcov : Analyzer.Covers SessionLayout.size s.memaddrs b) {k n : Nat}
    (hk : k + n ≤ nextLen) : ∀ i, i < n → s.memaddrs (byteAlign (nextW b k + BitVec.ofNat 64 i)) = true := by
  intro i hi
  have h0 := next_in (x := k + i) (by omega)
  have h1 := next_in (x := k) (by omega)
  exact byte_dom hcov (x := nextOff + k) h1.1 i (by omega)

/-- **Every slot of the batch reads as an event**, unless its index is in the table and its kind unknown. The
program stops on such a slot (`unknownEvent`). -/
theorem event_cases {s : PancakeState σ} {b : Word} (hcov : Analyzer.Covers SessionLayout.size s.memaddrs b) {e : Nat}
    (he : e < SessionLayout.batch) :
    (∃ ev, EventAt b e ev s) ∨ ((s.memory (evW b e eventIdx)).toNat < SessionLayout.conns ∧
      ((s.memory (evW b e eventKind)).toNat < SessionLayout.opened ∨
        SessionLayout.verified < (s.memory (evW b e eventKind)).toNat)) := by
  generalize hI : (s.memory (evW b e eventIdx)).toNat = I
  generalize hG : (s.memory (evW b e eventGen)).toNat = G
  by_cases hi : I < SessionLayout.conns
  · generalize hK : s.memory (evW b e eventKind) = K
    have hk : ∀ c : Nat, K.toNat = c → s.memory (evW b e eventKind) = BitVec.ofNat 64 c := fun c h => by
      rw [hK]
      exact BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← h]; exact K.isLt)])
    by_cases hu : K.toNat < SessionLayout.opened ∨ SessionLayout.verified < K.toNat
    · exact .inr ⟨hi, hu⟩
    left
    have h6 : K.toNat = 1 ∨ K.toNat = 2 ∨ K.toNat = 3 ∨ K.toNat = 4 ∨ K.toNat = 5 ∨ K.toNat = 6 := by
      have h1 : SessionLayout.opened = 1 := rfl
      have h2 : SessionLayout.verified = 6 := rfl
      omega
    rcases h6 with h | h | h | h | h | h
    · exact ⟨.opened I G (flag (s.memory (evW b e eventPost))) (flag (s.memory (evW b e eventLogins)))
        (flag (s.memory (evW b e eventTls))), hI, fun _ => hk _ h, fun _ => hG, fun _ => ⟨rfl, rfl, rfl⟩⟩
    · generalize hL : (s.memory (evW b e eventLen)).toNat = L
      by_cases hl : L ≤ data
      · have hS : eventSlot = eventHead + data := rfl
        have hle := event_le he (k := eventHead + L) (by omega)
        obtain ⟨ys, hyl, hys⟩ := Bytes.bytes_exist (u := s) (a := evW b e eventHead) L
          (next_bytes hcov (k := nextEvents + e * eventSlot + eventHead) (by omega))
        exact ⟨.received I G ys, hI, fun _ => hk _ h, fun _ => hG,
          fun _ => ⟨by rw [hL]; exact hyl, fun _ => hys⟩⟩
      · exact ⟨.received I G (List.replicate L 0), hI, fun _ => hk _ h, fun _ => hG,
          fun _ => ⟨by simp [hL], fun h' => absurd (by simpa using h') hl⟩⟩
    · exact ⟨.writable I G, hI, fun _ => hk _ h, fun _ => hG, fun _ => trivial⟩
    · exact ⟨.inputEnded I G, hI, fun _ => hk _ h, fun _ => hG, fun _ => trivial⟩
    · exact ⟨.closed I G, hI, fun _ => hk _ h, fun _ => hG, fun _ => trivial⟩
    · exact ⟨.verified I G (flag (s.memory (evW b e eventPost))), hI, fun _ => hk _ h, fun _ => hG, fun _ => rfl⟩
  · exact .inl ⟨.closed I 0, hI, fun h => absurd h hi, fun h => absurd h hi, fun h => absurd h hi⟩

/-- **Every completion slot reads as a completion.** -/
theorem done_of {s : PancakeState σ} {b : Word} (hcov : Analyzer.Covers SessionLayout.size s.memaddrs b) {j : Nat}
    (hj : j < jobs) : ∃ d, DoneAt b j d s := by
  cases hr : resultsOf b j s with
  | nil => exact ⟨{ slot := j, gen := _, ok := _, results := [], data := [] }, rfl, rfl, rfl, hr.symm, rfl⟩
  | cons r rs =>
    obtain ⟨g, w⟩ := r
    by_cases hg : g ≤ jobData
    · have hS : doneSlot = doneHead + jobData := rfl
      have hle := done_le hj (k := doneHead + g) (by omega)
      obtain ⟨ys, hyl, hys⟩ := Bytes.bytes_exist (u := s) (a := doneW b j doneHead) g
        (next_bytes hcov (k := nextDone + j * doneSlot + doneHead) (by omega))
      exact ⟨{ slot := j, gen := _, ok := _, results := (g, w) :: rs, data := ys }, rfl, rfl, rfl, hr.symm,
        by simp only [hg, if_true]; exact ⟨hyl, hys⟩⟩
    · exact ⟨{ slot := j, gen := _, ok := _, results := (g, w) :: rs, data := [] }, rfl, rfl, rfl, hr.symm,
        by simp only [hg, if_false]⟩

/-- **The array's words hold a batch** of as many events as its count says. That holds unless one of those slots has an
index in the table and an unknown kind. -/
theorem batch_of {s : PancakeState σ} {b : Word} (hcov : Analyzer.Covers SessionLayout.size s.memaddrs b)
    (hk : ∀ e, e < (s.memory (nextW b nextCount)).toNat → e < SessionLayout.batch → ∃ ev, EventAt b e ev s) :
    ∃ events slots,
      BatchAt b (s.memory (nextW b nextClock)).toNat (s.memory (nextW b nextWall)).toNat events slots s := by
  classical
  let n := (s.memory (nextW b nextCount)).toNat
  let evOf : Nat → Event := fun e => if h : ∃ ev, EventAt b e ev s then Classical.choose h else .closed 0 0
  let dnOf : Nat → Option Done := fun j =>
    if s.memory (doneW b j doneKind) = 0 then none
    else if h : ∃ d, DoneAt b j d s then some (Classical.choose h) else none
  refine ⟨(List.range n).map evOf, (List.range jobs).map dnOf, rfl, rfl, by simp [n], fun hn e he => ?_, by simp,
    fun j hj => ?_⟩
  · simp only [List.length_map, List.length_range] at he hn
    have hx := hk e he (by omega)
    simp only [List.getElem_map, List.getElem_range, evOf, dif_pos hx]
    exact Classical.choose_spec hx
  · have hd : ((List.range jobs).map dnOf).getD j none = dnOf j := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
    rw [hd]
    by_cases h0 : s.memory (doneW b j doneKind) = 0
    · simp only [dnOf, h0, if_true]
    · have hx := done_of hcov hj
      simp only [dnOf, h0, if_false, dif_pos hx]
      exact ⟨h0, Classical.choose_spec hx⟩

/-! ## `dn_emit` -/

/-- Word `k` of the `dn_emit` array. -/
def emitW (b : Word) (k : Nat) : Word := b + BitVec.ofNat 64 (emitOff + k)
/-- Word `k` of connection `c`'s action slot. -/
def actW (b : Word) (c k : Nat) : Word := emitW b (emitActions + c * actionSlot + k)
/-- Word `k` of job slot `j`. -/
def jobW (b : Word) (j k : Nat) : Word := emitW b (emitJobs + j * jobSlot + k)
/-- Word `k` of job slot `j`'s operation `i`. -/
def opW (b : Word) (j i k : Nat) : Word := jobW b j (jobOpsAt + i * opSlot + k)

/-- An action's kind, as its slot codes it. -/
def actKind : Action → Nat
  | .send .. => SessionLayout.send
  | .closeGracefully .. => SessionLayout.closeGracefully
  | .closeNow .. => SessionLayout.closeNow
  | .verify .. => SessionLayout.verify

/-- An action's generation. -/
def actGen : Action → Nat
  | .send _ g .. | .closeGracefully _ g | .closeNow _ g | .verify _ g .. => g

/-- **Connection `c`'s action slot holds `a`**: none as kind zero. The count taken is zero till the host writes it. A
check carries the name, then the password, the name's length where a send says whether to read. -/
def ActionAt (b : Word) (c : Nat) (s : PancakeState σ) : Option Action → Prop
  | none => s.memory (actW b c actionKind) = 0
  | some a => s.memory (actW b c actionKind) = BitVec.ofNat 64 (actKind a) ∧ a.idx = c ∧
    NumW s (actW b c actionIdx) c ∧ NumW s (actW b c actionGen) (actGen a) ∧ s.memory (actW b c actionTaken) = 0 ∧
    match a with
    | .send _ _ bs rd => NumW s (actW b c actionLen) bs.length ∧ bs.length ≤ data ∧
      s.memory (actW b c actionRead) = bw rd ∧ Chunk s (actW b c actionHead) bs
    | .verify _ _ nm pw => NumW s (actW b c actionLen) (nm.length + pw.length) ∧
      NumW s (actW b c actionRead) nm.length ∧ nm.length + pw.length ≤ data ∧
      Chunk s (actW b c actionHead) (nm ++ pw)
    | _ => s.memory (actW b c actionLen) = 0 ∧ s.memory (actW b c actionRead) = 0

/-- A name's kind and number, as an operation codes them. -/
def nameCode : News.Journal.Name → Nat × Nat
  | .journal => (nameJournal, 0)
  | .final q => (nameFinal, q)
  | .temp q => (nameTemp, q)
  | .quarantine q => (nameQuarantine, q)
  | .tail q => (nameTail, q)

/-- An operation's code, then its words. They are a file's place and generation, a name's kind and number, a second
name's, an offset and a length. -/
def opWords : News.PostSpec.Op → Nat × List Nat
  | .create n => (opCreate, [0, 0, (nameCode n).1, (nameCode n).2, 0, 0, 0, 0])
  | .write p g o bs => (opWrite, [p, g, 0, 0, 0, 0, o, bs.length])
  | .dataSync p g => (opDataSync, [p, g, 0, 0, 0, 0, 0, 0])
  | .close p g => (opClose, [p, g, 0, 0, 0, 0, 0, 0])
  | .rename a c => (opRename, [0, 0, (nameCode a).1, (nameCode a).2, (nameCode c).1, (nameCode c).2, 0, 0])
  | .remove n => (opRemove, [0, 0, (nameCode n).1, (nameCode n).2, 0, 0, 0, 0])
  | .syncDir => (opSyncDir, [0, 0, 0, 0, 0, 0, 0, 0])
  | .open_ n => (opOpen, [0, 0, (nameCode n).1, (nameCode n).2, 0, 0, 0, 0])
  | .read p g o len => (opRead, [p, g, 0, 0, 0, 0, o, len])

/-- Operation `i` of job slot `j` holds `op`; where its octets lie is zero, the job's first. -/
def OpAt (b : Word) (j i : Nat) (op : News.PostSpec.Op) (s : PancakeState σ) : Prop :=
  s.memory (opW b j i opCode) = BitVec.ofNat 64 (opWords op).1 ∧ s.memory (opW b j i opData) = 0 ∧
    ∀ k (h : k < (opWords op).2.length), WordN s (opW b j i (8 * (k + 1))) (opWords op).2[k]

/-- **Job slot `j` holds `jb`**: none as kind zero. Else it holds its generation, its operations, and a write's octets
first in its data. -/
def JobAt (b : Word) (j : Nat) (s : PancakeState σ) : Option News.PostSpec.Job → Prop
  | none => s.memory (jobW b j jobKind) = 0
  | some jb => jb.slot = j ∧ s.memory (jobW b j jobKind) = BitVec.ofNat 64 SessionLayout.job ∧
    NumW s (jobW b j jobGen) jb.gen ∧ NumW s (jobW b j jobCount) jb.ops.length ∧ jb.ops.length ≤ jobOps ∧
    (∀ i (h : i < jb.ops.length), OpAt b j i jb.ops[i] s) ∧
    ∀ (i p g o : Nat) bs, jb.ops[i]? = some (.write p g o bs) →
      bs.length ≤ jobData ∧ Chunk s (jobW b j jobHead) bs

/-- **The `dn_emit` array holds the turn's actions and jobs**: a slot for each connection and each job. It also holds
the actions' count. -/
structure HandAt (b : Word) (acts : List (Option Action)) (jbs : List (Option News.PostSpec.Job))
    (s : PancakeState σ) : Prop where
  count : NumW s (emitW b emitCount) (acts.filterMap id).length
  acts_len : acts.length = SessionLayout.conns
  acts : ∀ c (h : c < acts.length), ActionAt b c s acts[c]
  jobs_len : jbs.length = jobs
  jobs : ∀ j (h : j < jbs.length), JobAt b j s jbs[j]

/-- Whether an action is a check, which carries no output. -/
def Action.isVerify : Action → Bool
  | .verify .. => true
  | _ => false

/-- **What the host took**, as `settleTable` takes it: each send's count, in the order of the actions. A check's
count, read as a send's is, is one more past the sends when not zero: `overTaken` either way. -/
def takenOf (b : Word) (acts : List (Option Action)) (s : PancakeState σ) : List Nat :=
  let ws := acts.zipIdx.filterMap fun
    | (some (.send ..), c) => some (s.memory (actW b c actionTaken)).toNat
    | _ => none
  if acts.zipIdx.any fun (a, c) => (a.any Action.isVerify) && s.memory (actW b c actionTaken) != 0 then ws ++ [0]
  else ws

/-- The `dn_emit` array lies past the `dn_next` array and within the session's words. -/
theorem emit_in : nextOff + nextLen ≤ emitOff ∧ emitOff % 8 = 0 ∧ emitOff + emitLen ≤ SessionLayout.size := by
  obtain ⟨-, -, h2, h3, h4, -, h6, -⟩ := areas_disjoint
  have h4' : ownOff ≤ tableOff := Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) h4
  have h6' : tableOff ≤ SessionLayout.size :=
    Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) h6
  refine ⟨h2, offsets_aligned.2.2.2.2.2.1, ?_⟩
  clear h4 h6
  generalize SessionLayout.size = S at h6' ⊢
  generalize tableOff = T at h4' h6'
  generalize ownOff = O at h3 h4'
  omega

/-- **`dn_emit` writes only its array.** -/
theorem hand_frag (o : Oracle σ) {s0 : PancakeState σ} {b : Word} (hb0 : s0.baseAddr = b) (hb : b.toNat % 8 = 0)
    (hcov : Analyzer.Covers SessionLayout.size s0.memaddrs b) {l : List (String × Value)} {M : Word → Word} :
    Frag o [Session.hand] (RunF s0 l (· = M))
      (fun u => ∃ M', RunF s0 l (· = M') u ∧ ∀ y, y < 2 ^ 64 → (y < emitOff ∨ emitOff + emitLen ≤ y) →
        M' (b + BitVec.ofNat 64 y) = M (b + BitVec.ofNat 64 y)) :=
  have he := emit_in
  have hn := next_in (x := 0) (by decide)
  call_frag o he.2.1 (by omega) he.2.2 hb0 hb hcov

/-! ## The premises can hold -/

/-- The heap all words addressable. -/
theorem zero_covers : Analyzer.Covers SessionLayout.size SessionState.zeroState.memaddrs 0 :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- A batch of no event and no completion; an event's slot and a completion's. -/
theorem batchAt_witness : BatchAt 0 0 0 [] (List.replicate jobs none) SessionState.zeroState where
  clock := rfl
  wall := rfl
  count := rfl
  events := fun _ e h => absurd h (by simp)
  len := by simp
  dones := fun j hj => by simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hj]; rfl

def fiveState : PancakeState Unit := { SessionState.zeroState with memory := fun _ => 5 }

theorem eventAt_witness : EventAt 0 0 (.closed 5 5) fiveState := ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => trivial⟩

theorem doneAt_witness : ∃ d, DoneAt 0 0 d SessionState.zeroState := done_of zero_covers (by decide)

/-- An array of no action and no job; an action's slot. -/
theorem handAt_witness : HandAt 0 (List.replicate SessionLayout.conns none) (List.replicate jobs none)
    SessionState.zeroState where
  count := ⟨by simp; rfl, by simp⟩
  acts_len := by simp
  acts := fun c h => by simp only [List.getElem_replicate]; rfl
  jobs_len := by simp
  jobs := fun j h => by simp only [List.getElem_replicate]; rfl

def closeState : PancakeState Unit :=
  { SessionState.zeroState with memory := fun a => if a = actW 0 0 actionKind then 3 else 0 }

theorem actionAt_witness : ActionAt 0 0 closeState (some (.closeNow 0 0)) := by
  have h : ∀ k, k ≠ actionKind → k < actionSlot → closeState.memory (actW 0 0 k) = 0 := fun k hk hs => by
    simp only [closeState, actW, emitW]
    have h1 : emitOff + (emitActions + 0 * actionSlot + actionSlot) < 2 ^ 64 := by decide
    rw [if_neg fun e => hk (by
      have := DN.News.ScanRun.at_inj (A := 0) (by omega) (by have : actionKind = 0 := rfl; omega) e
      omega)]
  refine ⟨by simp only [closeState, if_true]; rfl, rfl, ⟨h _ (by decide) (by decide), by decide⟩,
    ⟨h _ (by decide) (by decide), by decide⟩, h _ (by decide) (by decide), h _ (by decide) (by decide),
    h _ (by decide) (by decide)⟩

/-- A heap of the words `ws`, by address, zero elsewhere. -/
def wordsMem (ws : List (Nat × Nat)) (a : Word) : Word :=
  match ws.find? (fun w => BitVec.ofNat 64 w.1 == a) with
  | some w => BitVec.ofNat 64 w.2
  | none => 0

/-- A send in slot zero, a check in slot one, a job of one write in job slot zero. -/
def handState : PancakeState Unit :=
  { SessionState.zeroState with memory := wordsMem [(792152, 1), (792176, 1), (792184, 1), (792200, 65),
      (792712, 4), (792720, 1), (792736, 2), (792744, 1), (792760, 16961), (827992, 1), (828000, 1), (828008, 1),
      (828016, 3), (828032, 1), (828080, 1), (828656, 65)] }

theorem hand_nums : emitOff = 792136 ∧ emitActions = 16 ∧ actionSlot = 560 ∧ emitJobs = 35856 ∧ jobSlot = 17048 ∧
    jobOpsAt = 24 ∧ opSlot = 80 ∧ jobHead = 664 := by decide

theorem sendAt_witness : ActionAt 0 0 handState (some (.send 0 0 [65] true)) := by
  obtain ⟨h1, h2, h3, -⟩ := hand_nums
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, by decide, ?_, fun j hj => ?_⟩
  all_goals try simp only [actW, emitW, NumW, h1, h2, h3]
  all_goals try decide
  obtain rfl : j = 0 := by simp at hj; omega
  simp only [List.getElem_cons_zero]
  decide

theorem verifyAt_witness : ActionAt 0 1 handState (some (.verify 1 0 [65] [66])) := by
  obtain ⟨h1, h2, h3, -⟩ := hand_nums
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, by decide, fun j hj => ?_⟩
  all_goals try simp only [actW, emitW, NumW, h1, h2, h3]
  all_goals try decide
  rcases (by simp at hj; omega : j = 0 ∨ j = 1) with rfl | rfl <;>
    simp only [List.cons_append, List.nil_append, List.getElem_cons_zero, List.getElem_cons_succ] <;> decide

theorem jobAt_witness : JobAt 0 0 handState (some ⟨0, 1, [.write 0 1 0 [65]]⟩) := by
  obtain ⟨h1, -, -, h4, h5, h6, h7, h8⟩ := hand_nums
  refine ⟨rfl, ?_, ?_, ?_, by decide, fun i hi => ?_, fun i p g o bs h => ?_⟩
  · simp only [jobW, emitW, h1, h4, h5]; decide
  · simp only [NumW, jobW, emitW, h1, h4, h5]; decide
  · simp only [NumW, jobW, emitW, h1, h4, h5]; decide
  · obtain rfl : i = 0 := by simp at hi; omega
    show OpAt 0 0 0 (.write 0 1 0 [65]) handState
    simp only [OpAt, WordN, opW, jobW, emitW, h1, h4, h5, h6, h7]
    decide
  · obtain ⟨rfl, -⟩ : i = 0 ∧ True := ⟨by cases i <;> simp_all, trivial⟩
    simp only [List.getElem?_cons_zero, Option.some.injEq, News.PostSpec.Op.write.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    refine ⟨by decide, ?_⟩
    simp only [Chunk, jobW, emitW, h1, h4, h5, h8]
    decide

end DN.Server.SessionHost
