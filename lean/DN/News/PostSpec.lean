-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleSpec
import DN.News.Framer
import DN.News.Recovery

/-!
# DN.News.PostSpec

The store's side of POST as docs/decisions/0005-article-store.md fixes it, apart from the program
that runs it: four slots, each holding the article of one POST from its 340 until its last file
job ends. `DN.News.SessionSpec` runs it for the connections.

An article is framed as it arrives (`Framer.blockStep`) and its octets counted, the terminator
among them. Its header section is gathered and checked when the empty line ends it
(`ArticleSpec.check`), and a block that ends before it is refused; a Message-ID the store holds or
another slot has reserved, a store at its capacity, or no sequence number left refuses it too. Its
file is the header section stored with what was added, the empty line and the body, dots stuffed
as a reader receives them, written in jobs of `jobData` octets as they come; meanwhile the slot
takes no more octets. Once the block ends: the rest written, the file synced and closed; renamed
to its final name and the directory synced; the commit appended and the journal synced, its
article numbers allocated then; 240.

A slot runs one job at a time, each within what one job may hold (`nextJob_fits`); one sync of the
directory and one append of the journal are in flight across all of them. A job failing before the
commit refuses the article (441) and its names are removed, a failed close leaving the removal to a
job of its own; a failed sync or close also stops the store accepting, and then every article not
committing is refused once its job in flight ends. A failed append or sync of the journal leaves
the outcome unknown: the connection is closed without an answer, the store stops accepting, and so
does a commit whose sync completes after the store has stopped. POSTs waiting for a slot get one in
the order they came (`Store.waiters`). A completion the host may not report ends the run
(`Fault`). The rules a version with one broken shows to matter (`DN.News.SessionMutant`) are
fields of the store's `Rules`, the specification's being the defaults.
-/

namespace DN.News.PostSpec

open DN.News.FrameSpec DN.News.Framer
open DN.News.ArticleSpec (Context Accepted Verdict check)
open DN.News.Journal (Commit Group Record Name crc32c)
open DN.News.Recovery (highIn)
open DN.News.CommandSpec (crlf)

/-- Jobs in flight, the operations of one and the octets it moves; places of open files (0005,
"File operations through the host"). -/
def jobs : Nat := 8
def jobOps : Nat := 8
def jobData : Nat := 16384
def places : Nat := 16
def headerMax : Nat := ArticleSpec.spec.headerMax

/-- The rules and bounds of the store's side. -/
structure Rules where
  /-- 0005: POSTs at once -/
  posts : Nat := 4
  /-- 0005: the octets an article arrives in, its terminator counted -/
  articleMax : Nat := 1000000
  /-- RFC 3977 §3.1.1: a dot put before a line of the file that starts with one -/
  stuffs : Bool := true
  /-- 0005: a Message-ID another slot has reserved refused -/
  reserves : Bool := true
  /-- 0005: the file synced before it is closed, the directory after the rename, the journal after
  the append -/
  syncsFile : Bool := true
  syncsDir : Bool := true
  syncsJournal : Bool := true
  /-- 0005: one sync of the directory, and one append of the journal, in flight -/
  oneDirSync : Bool := true
  oneAppend : Bool := true
  /-- RFC 3977 §6: an article's number above the group's highest -/
  numbersAbove : Bool := true
  /-- 0005: a failed sync or close stops the store accepting -/
  stops : Bool := true
  /-- 0005: a failed append or sync of the journal leaves the outcome unknown -/
  unknown : Bool := true
  /-- 0005: a refused article's names removed -/
  cleans : Bool := true
  /-- RFC 3977 §3.6: a block that ends before the empty line refused -/
  separates : Bool := true
  /-- 0005: the articles the store holds, files set aside and articles reserved counted -/
  capacity : Nat := Recovery.capacity
  /-- 0005: a refused article's Message-ID no longer reserved -/
  releases : Bool := true
  /-- 0005: once the store stops accepting, every article not committing refused -/
  refusesInFlight : Bool := true
  /-- 0005: a commit whose sync completes after the store has stopped not answered -/
  distrusts : Bool := true

/-- An operation of a file job. -/
inductive Op
  | create (n : Name)
  | write (place gen offset : Nat) (data : List Byte)
  | dataSync (place gen : Nat)
  | close (place gen : Nat)
  | rename (src dst : Name)
  | remove (n : Name)
  | syncDir
  deriving DecidableEq

/-- A job handed to the host: its slot, its generation and its operations. -/
structure Job where
  slot : Nat
  gen : Nat
  ops : List Op
  deriving DecidableEq

/-- A job's completion: its slot and generation, how many operations succeeded, and the two result
words of each that did. -/
structure Done where
  slot : Nat
  gen : Nat
  ok : Nat
  results : List (Nat × Nat)
  deriving DecidableEq

/-- What a host may not report of a job; each ends the run. -/
inductive Fault
  /-- a completion of no job in flight -/
  | unknownJob
  /-- more operations done than the job had, results for none, or a place past the table -/
  | badDone
  deriving DecidableEq, Repr

/-- What the job in flight of a slot does: create the file; write `len` octets; write the rest,
`len` octets in `writes` operations, sync and close; place the file; append the commit, a frame of
`len` octets; remove the names, closing the file first when `closes`. -/
inductive Task
  | create
  | write (len : Nat)
  | finish (writes len : Nat)
  | place
  | commit (c : Commit) (len : Nat)
  | clean (closes : Bool)
  deriving DecidableEq

/-- Where an accepted article's file has come. -/
inductive File
  | none
  /-- created under the temporary name, open at a place -/
  | open_ (place gen : Nat)
  /-- written whole, synced and closed -/
  | closed
  /-- moved to the final name, the directory not synced -/
  | final
  /-- moved and the directory synced -/
  | placed
  deriving DecidableEq

/-- An article accepted so far: its number, its message identifier, the groups it is stored in,
the size of its header section in the file, the file's octets known, how many are written. -/
structure Article where
  seq : Nat
  messageId : List Byte
  groups : List (List Byte)
  headerSize : Nat
  octets : Array Byte
  written : Nat
  file : File
  deriving DecidableEq

inductive Outcome
  /-- 240 -/
  | posted
  /-- 441 -/
  | failed
  /-- unknown: the connection closed without an answer -/
  | lost
  deriving DecidableEq

/-- A POST: the connection that posts, until it is answered or gone, and its number; the framer,
the octets arrived, whether the block has ended; the header section's lines so far, dots unstuffed,
until the empty line, then whether the next octet of the file starts a line; the article accepted
so far; whether it is refused; its outcome; its job in flight, by slot, generation, operations and
task. -/
structure Slot where
  owner : Option (Nat × Nat)
  conn : Nat
  frame : BlockState := .fresh
  arrived : Nat := 0
  ended : Bool := false
  header : Array Byte := #[]
  body : Bool := false
  bol : Bool := true
  article : Option Article := none
  refused : Bool := false
  outcome : Option Outcome := none
  busy : Option (Nat × Nat × Nat × Task) := none
  deriving DecidableEq

/-- What the host gives the store: the groups, the path identity, the run's value in hexadecimal
digits as Message-IDs carry it and as a number as Injection-Info does. -/
structure Config where
  groups : List (List Byte)
  identity : List Byte
  random : List Byte
  run : Nat

/-- The store while the session runs: its rules and configuration; the journal's key, its commits,
where it ends and its place; the numbers set aside and the next to give; whether it accepts; the
generation of the last job; the slots; the connections whose POST waits for one, by index and
generation, in the order they came. -/
structure Store where
  rules : Rules := {}
  cfg : Config
  key : List Byte
  articles : List Commit
  setAside : List Nat
  next : Nat
  journalEnd : Nat
  journal : Nat × Nat
  accepting : Bool := true
  jobGen : Nat
  slots : List (Option Slot)
  waiters : List (Nat × Nat) := []

/-- The store a recovered spool starts, the start record already appended where it ended. -/
def Store.start (rules : Rules) (cfg : Config) (st : Recovery.Store) (journal : Nat × Nat)
    (jobGen : Nat) : Store :=
  { rules, cfg, key := st.key, articles := st.articles, setAside := st.setAside, next := st.next,
    journalEnd := st.journalEnd, journal, jobGen, slots := List.replicate rules.posts none }

/-- Whether slot `k` is free. -/
def Store.free (st : Store) (k : Nat) : Bool := (st.slots[k]?).any Option.isNone

/-- Whether the POST of a connection that waits gets a slot now: fewer came before it than slots are
free. -/
def Store.admits (st : Store) (w : Nat × Nat) : Bool :=
  match st.waiters.findIdx? (· == w) with
  | some n => n < ((List.range st.rules.posts).filter st.free).length
  | none => false

def Store.slot (st : Store) (k : Nat) : Option Slot := (st.slots[k]?).getD none

def Store.setSlot (st : Store) (k : Nat) (x : Option Slot) : Store :=
  { st with slots := st.slots.set k x }

/-! ## An article's octets -/

/-- One octet of a block, framed by `blockStep`: the state after it, the octets it adds to what
the block holds, and at the block's end whether the block is clean. -/
def frameOctet (s : BlockState) (x : Byte) : BlockState × List Byte × Option Bool :=
  match blockStep 2 { s with size := 0, buf := [] } x with
  | (s', some r) => (s', [], some (r.kind == .accepted))
  | (s', none) => ({ s' with size := 0, buf := [] }, s'.buf, none)

/-- One octet adds at most two to what the block holds: a CR held back, and the octet after it. -/
theorem frameOctet_adds (s : BlockState) (x : Byte) : (frameOctet s x).2.1.length ≤ 2 := by
  have h : (blockStep 2 { s with size := 0, buf := [] } x).1.buf.length ≤ 2 := by
    unfold blockStep
    cases s.phase <;> simp only [] <;> (repeat' split) <;> simp [put, BlockState.at, BlockState.fresh]
  unfold frameOctet
  split
  · simp
  · rename_i s' heq
    rw [heq] at h
    exact h

/-- Octets of lines as a reader receives them: a dot put before a line that starts with one;
`bol` whether the first octet starts a line, and the same after the last. -/
def stuff (bol : Bool) : List Byte → List Byte × Bool
  | [] => ([], bol)
  | x :: rest =>
    let (out, b) := stuff (x == LF) rest
    ((if bol && x == DOT then [DOT, x] else [x]) ++ out, b)

def Rules.stuff (r : Rules) (bol : Bool) (o : List Byte) : List Byte × Bool :=
  if r.stuffs then PostSpec.stuff bol o else (o, bol)

/-- Whether the header section's lines so far end with the empty line. -/
def endsHeader (h : Array Byte) : Bool :=
  h.toList == crlf || (4 ≤ h.size && (h.extract (h.size - 4) h.size).toList == crlf ++ crlf)

/-- The octets of the file known and not yet written. -/
def Article.pending (a : Article) : Nat := a.octets.size - a.written

/-- Whether a slot takes more octets: its block goes on, and fewer than a job's octets wait to be
written. A write is started only with as many waiting, and counted written only once it has
completed, so no octet is taken while a write is in flight. -/
def Slot.takes (s : Slot) : Bool :=
  !s.ended && (s.article.map fun a => decide (a.pending < jobData)).getD true

/-- The Message-IDs the slots hold reserved: those of their articles not refused. -/
def Store.reserved (st : Store) : List (List Byte) :=
  st.slots.filterMap fun x =>
    x.bind fun s => if s.refused && st.rules.releases then none else s.article.map (·.messageId)

def Store.context (st : Store) (wall conn : Nat) : Context :=
  { groups := st.cfg.groups, identity := st.cfg.identity, wall := wall / 1000, seq := st.next,
    random := st.cfg.random, run := st.cfg.run, conn }

/-- The header section ended: checked, its Message-ID reserved and a sequence number given, or the
article refused. -/
def Store.accept (st : Store) (wall : Nat) (s : Slot) : Store × Slot :=
  match check (st.context wall s.conn) s.header.toList with
  | .refused _ => (st, { s with refused := true, body := true })
  | .accepted a =>
    if st.articles.any (·.messageId == a.messageId) ||
        (st.rules.reserves && st.reserved.contains a.messageId) ||
        st.rules.capacity ≤ st.articles.length + st.setAside.length + st.reserved.length ||
        2 ^ 64 ≤ st.next + 2 then (st, { s with refused := true, body := true })
    else
      let head := (st.rules.stuff true a.header).1
      let art : Article :=
        ⟨st.next, a.messageId, a.groups, head.length, (head ++ crlf).toArray, 0, .none⟩
      ({ st with next := st.next + 1 }, { s with body := true, bol := true, article := some art })

/-- One octet of the block into the slot. -/
def Store.octet (wall : Nat) (st : Store) (s : Slot) (x : Byte) : Store × Slot :=
  let (f, add, fin) := frameOctet s.frame x
  let s := { s with frame := f, arrived := s.arrived + 1 }
  match fin with
  | some clean =>
    let long := st.rules.articleMax < s.arrived
    let early := st.rules.separates && !s.body
    (st, { s with ended := true, refused := s.refused || !clean || long || early })
  | none =>
    if s.refused then (st, s)
    else if f.bad || st.rules.articleMax < s.arrived then (st, { s with refused := true })
    else if !s.body then
      let h := s.header
      let h := add.foldl Array.push h
      let s := { s with header := #[] }
      if headerMax < h.size && !endsHeader h then (st, { s with refused := true })
      else if endsHeader h then st.accept wall { s with header := h }
      else (st, { s with header := h })
    else
      match s.article with
      | some a =>
        let s := { s with article := none }
        let (o, b) := st.rules.stuff s.bol add
        (st, { s with article := some { a with octets := o.foldl Array.push a.octets }, bol := b })
      | none => (st, s)

/-- Held octets framed into slot `k` while it takes them; what is left of them. -/
def Store.feed (wall k : Nat) : Nat → Store → List Byte → Store × List Byte
  | 0, st, held => (st, held)
  | _, st, [] => (st, [])
  | fuel + 1, st, x :: rest =>
    match st.slot k with
    | some s => if s.takes then
        let (st, s) := (st.setSlot k none).octet wall s x
        Store.feed wall k fuel (st.setSlot k (some s)) rest
      else (st, x :: rest)
    | none => (st, x :: rest)

/-! ## Deciding -/

/-- Whether the slot's job in flight appends the journal, or syncs the directory. -/
def Slot.committing (s : Slot) : Bool :=
  match s.busy with | some (_, _, _, .commit ..) => true | _ => false
def Slot.placing (s : Slot) : Bool :=
  match s.busy with | some (_, _, _, .place) => true | _ => false

/-- What a slot decides without the host: an article not committing refused once the store stops
accepting; 441 once a refused block has ended and no job is in flight; an article with no file
forgotten once refused; the slot freed once it has no owner, no job and no article. -/
def Slot.tidy (r : Rules) (accepting : Bool) (s : Slot) : Option Slot :=
  let s := if !accepting && r.refusesInFlight && s.outcome.isNone && !s.committing then
    { s with refused := true } else s
  let s := if s.outcome.isNone && s.refused && s.ended && s.busy.isNone then
    { s with outcome := some .failed } else s
  let s := if s.refused && s.busy.isNone && (s.article.map (·.file == .none)).getD false then
    { s with article := none } else s
  if s.owner.isNone && s.busy.isNone && s.article.isNone then none else some s

def Store.tidy (st : Store) : Store :=
  { st with slots := st.slots.map (·.bind (Slot.tidy st.rules st.accepting)) }

/-- The connection `idx` of generation `gen` gone, or no longer reading: its slot's article, if
the block has not ended, abandoned, and its POST no longer waiting. -/
def Slot.leftBy (idx gen : Nat) (s : Slot) : Slot :=
  if s.owner == some (idx, gen) then { s with owner := none, refused := s.refused || !s.ended }
  else s

def Store.abandon (idx gen : Nat) (st : Store) : Store :=
  Store.tidy { st with slots := st.slots.map (·.map (Slot.leftBy idx gen)),
                       waiters := st.waiters.erase (idx, gen) }

/-! ## Jobs -/

/-- The ops of the job that cleans an article's names up. -/
def cleanOps (r : Rules) (a : Article) : List Op × Bool :=
  if !r.cleans then ([], false) else
  match a.file with
  | .open_ p g => ([.close p g, .remove (.temp a.seq)], true)
  | .closed => ([.remove (.temp a.seq)], false)
  | .final | .placed => ([.remove (.final a.seq)], false)
  | .none => ([], false)

/-- The commit of an article placed: its article numbers next in each group. -/
def Store.commitOf (st : Store) (a : Article) : Commit :=
  let above := if st.rules.numbersAbove then 1 else 0
  ⟨a.seq, a.messageId, a.groups.map fun g => ⟨g, highIn st.articles g + above⟩, a.headerSize,
    a.octets.size, (crc32c a.octets.toList).toNat⟩

/-- The next job of a slot, if it has one to start, with what it does; or the article refused, when
its commit cannot be made. -/
def Store.nextJob (st : Store) (s : Slot) : Option (List Op × Task) ⊕ Slot :=
  match s.busy, s.article with
  | some _, _ | none, none => .inl none
  | none, some a =>
    if s.refused then
      let (ops, closes) := cleanOps st.rules a
      .inl (if ops.isEmpty then none else some (ops, .clean closes))
    else if s.outcome.isSome then .inl none
    else match a.file with
    | .none => .inl (some ([.create (.temp a.seq)], .create))
    | .open_ p g =>
      let rest := (a.octets.extract a.written a.octets.size).toList
      if jobData ≤ a.pending then
        let chunk := (a.octets.extract a.written (a.written + jobData)).toList
        .inl (some ([.write p g a.written chunk], .write jobData))
      else if s.ended then
        let w := if rest.isEmpty then [] else [Op.write p g a.written rest]
        let sync := if st.rules.syncsFile then [Op.dataSync p g] else []
        .inl (some (w ++ sync ++ [.close p g], .finish w.length rest.length))
      else .inl none
    | .closed =>
      if st.rules.oneDirSync && st.slots.any (·.any Slot.placing) then .inl none
      else
        let sync := if st.rules.syncsDir then [Op.syncDir] else []
        .inl (some (.rename (.temp a.seq) (.final a.seq) :: sync, .place))
    | .placed =>
      if st.rules.oneAppend && st.slots.any (·.any Slot.committing) then .inl none
      else
        let c := st.commitOf a
        if (Record.commit c).ok then
          let fr := (Record.commit c).encode st.key st.journalEnd
          let sync := if st.rules.syncsJournal then [Op.dataSync st.journal.1 st.journal.2] else []
          let append := Op.write st.journal.1 st.journal.2 st.journalEnd fr
          .inl (some (append :: sync, .commit c fr.length))
        else .inr { s with refused := true }
    | .final => .inl none

/-- The octets an operation carries. -/
def Op.octets : Op → Nat
  | .write _ _ _ d => d.length
  | _ => 0

/-- **Every job a slot starts fits one**: at most `jobOps` operations and `jobData` octets, which
the host takes no more of. -/
theorem nextJob_fits (st : Store) (s : Slot) (ops : List Op) (t : Task)
    (h : st.nextJob s = .inl (some (ops, t))) :
    ops.length ≤ jobOps ∧ (ops.map Op.octets).sum ≤ jobData := by
  unfold Store.nextJob at h
  split at h
  · cases h
  · cases h
  · rename_i a
    split at h
    · simp only [cleanOps] at h
      split at h
      · cases h
      · split at h <;> (split at h <;> simp at h) <;>
          (obtain ⟨rfl, -⟩ := h; simp [Op.octets, jobOps, jobData])
    · split at h
      · cases h
      · split at h
        · simp only [Sum.inl.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          simp [Op.octets, jobOps, jobData]
        · dsimp only at h
          split at h
          · simp only [Sum.inl.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            simp only [List.length_singleton, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil, Op.octets, Array.length_toList, Array.size_extract, jobOps, jobData]
            omega
          · split at h
            · rename_i hp _
              simp only [Sum.inl.injEq, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              simp only [Article.pending, jobData] at hp
              constructor
              · split <;> split <;> simp [jobOps]
              · split <;> split <;>
                  simp [Op.octets, Array.length_toList, jobData] <;> omega
            · cases h
        · split at h
          · cases h
          · simp only [Sum.inl.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            split <;> simp [Op.octets, jobOps, jobData]
        · split at h
          · cases h
          · dsimp only at h
            split at h
            · rename_i hok
              simp only [Sum.inl.injEq, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              have hf := Journal.encode_le _ hok st.key st.journalEnd
              simp only [Journal.maxFrame, Journal.headerLength, Journal.maxPayload] at hf
              split <;> simp [Op.octets, jobOps, jobData] <;> omega
            · cases h
        · cases h

/-- The lowest job slot no job in flight holds. -/
def Store.freeJob (st : Store) : Nat :=
  ((List.range jobs).find? fun j =>
    !st.slots.any (·.any fun s => s.busy.any (·.1 == j))).getD 0

/-- Slot `k`'s next job started, if it has one. -/
def Store.plan (st : Store) (k : Nat) : Store × Option Job :=
  match st.slot k with
  | none => (st, none)
  | some s =>
    let start (st : Store) (s : Slot) (ops : List Op) (t : Task) : Store × Option Job :=
      let j := st.freeJob
      let gen := st.jobGen + 1
      ({ st with jobGen := gen }.setSlot k (some { s with busy := some (j, gen, ops.length, t) }),
       some ⟨j, gen, ops⟩)
    match st.nextJob s with
    | .inl none => (st, none)
    | .inl (some (ops, t)) => start st s ops t
    | .inr s =>
      match st.nextJob s with
      | .inl (some (ops, t)) => start st s ops t
      | _ => (st.setSlot k (some s), none)

/-- **The jobs of a turn**: each slot's next, in the order of the slots. -/
def Store.planAll (st : Store) : Store × List Job :=
  (List.range st.rules.posts).foldl (fun (st, js) k =>
    let (st, j) := st.plan k
    (st, js ++ j.toList)) (st, [])

/-! ## Completions -/

/-- The slot whose job in flight is the one completed. -/
def Store.findJob (st : Store) (d : Done) : Option Nat :=
  (List.range st.rules.posts).find? fun k =>
    (st.slot k).any fun s => s.busy.any fun b => b.1 == d.slot && b.2.1 == d.gen

/-- The store stopped accepting, by a failed sync or close. -/
def Store.stop (st : Store) : Store := if st.rules.stops then { st with accepting := false } else st

/-- What a completion does to the slot whose job it ends, and to whether the store accepts: the
last operation of a finish closes the file, the one before it syncs it. -/
def Store.complete (st : Store) (d : Done) : Except Fault Store := do
  let some k := st.findJob d | throw .unknownJob
  let some s := st.slot k | throw .unknownJob
  let some (_, _, n, t) := s.busy | throw .unknownJob
  if n < d.ok || d.results.length != d.ok then throw .badDone
  let s := { s with busy := none }
  let all := d.ok == n
  let withFile (s : Slot) (f : File) (more : Nat) : Slot :=
    { s with article := s.article.map fun a => { a with file := f, written := a.written + more } }
  match t with
  | .create =>
    match d.results with
    | [(p, g)] =>
      if places ≤ p then throw .badDone
      return st.setSlot k (some (withFile s (.open_ p g) 0))
    | _ => return st.setSlot k (some { s with refused := true })
  | .write len =>
    return st.setSlot k (some (if all then
      { s with article := s.article.map fun a => { a with written := a.written + len } }
      else { s with refused := true }))
  | .finish w len =>
    if all then return st.setSlot k (some (withFile s .closed len))
    else if d.ok < w then return st.setSlot k (some { s with refused := true })
    else if d.ok + 1 < n then return (st.setSlot k (some { s with refused := true })).stop
    else return (st.setSlot k (some (withFile { s with refused := true } .closed 0))).stop
  | .place =>
    if all then return st.setSlot k (some (withFile s .placed 0))
    else if d.ok = 1 then
      return (st.setSlot k (some (withFile { s with refused := true } .final 0))).stop
    else return st.setSlot k (some { s with refused := true })
  | .commit c len =>
    if all && (st.accepting || !st.rules.distrusts) then
      return { st.setSlot k (some { s with outcome := some .posted, article := none }) with
        articles := st.articles ++ [c], journalEnd := st.journalEnd + len }
    else
      let o := if st.rules.unknown then PostSpec.Outcome.lost else .failed
      return { st.setSlot k (some { s with outcome := some o, article := none }) with
        accepting := false }
  | .clean closes =>
    if closes && d.ok == 0 then return (st.setSlot k (some (withFile s .closed 0))).stop
    return st.setSlot k (some { s with article := none })

/-- A completion for a job slot past the table is no job's. -/
def Store.completeAll (st : Store) (ds : List Done) : Except Fault Store := do
  if jobs < ds.length then throw .badDone
  let st ← ds.foldlM Store.complete st
  return st.tidy

end DN.News.PostSpec
