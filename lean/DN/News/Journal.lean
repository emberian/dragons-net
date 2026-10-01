-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.CommandSpec
import DN.News.SipHash

/-!
# DN.News.Journal

The store's journal and the names of its files, as docs/decisions/0005-article-store.md ("On
disk") fixes them: how a record is framed, tagged and what it holds, the names of the store's
files, and how a journal is read back — its records in order, and how it ends: cleanly, in a torn
tail the next start truncates, or in corruption that keeps the store from starting. The CRC-32C a
commit gives of its article's file is defined here too.

A record is framed as `length ‖ tag ‖ type ‖ payload ‖ end`: the payload's length, four octets,
least significant first; the tag, eight octets, SipHash-2-4 under the journal's key of the frame's
offset, the type and the payload; the type, one octet; the payload; and the end mark, one octet.
The journal's first record names its format and carries the key. Each start of the store appends a
start record, with no payload, before anything else, and each other record is the commit of an
article: its number in the store, its message identifier, each group it goes to with the number it
has there, the size of its header section and of its file, and the file's CRC-32C. The start's
frame is the shortest (`start_shortest`): appended where a torn tail was truncated, it cannot leave
whole any frame cut away there.

Reading stops at the first frame that does not check. If it is short, its length past any
payload's, its end mark missing or its tag wrong — what an append the crash cut short can leave —
what is left is no longer than the one append that can have been cut, the format's frame while no
record has been read and the largest frame after, and no frame that checks starts in it after its
first octet, as none does after the last thing written, it is a torn tail, which the next start
truncates. Anything else is corruption, and so is, wherever it is, a frame that checks but holds no
record, a format of another version among them, and a format again. Before its format a journal
has no key, so its first frame is checked with the key it carries, which only a frame of the
format's shape does.

Proven: a journal of records reads back as those records (`scan_encoded`); after them, a frame cut
short reads as a torn tail where it starts, whether the crash left a proper prefix of it
(`scan_torn`), that prefix and zeros to the frame's length (`scan_torn_zeros`), or its length and
any octets to the frame's length but the end mark last (`scan_torn_fill`), whatever its tag, when no
frame that checks starts in what is left after its first octet (`Quiet`); so does the format's frame
cut short while it is alone (`scan_torn_format`, `scan_torn_format_zeros`, `scan_torn_format_fill`);
a frame that does not check, a record after it framed where it lies, is corruption (`scan_damaged`);
and reading looks at no octet past a frame it reads, so a journal read up to its torn tail reads the
same records and ends cleanly (`next_take`, `scan_take`). That the octets a crash leaves never make
a frame whose tag checks where it was not written is assumed: it takes the key.
-/

namespace DN.News.Journal

open DN.News.FrameSpec
open DN.News.CommandSpec (ascii)

abbrev Bytes := List Byte

/-! ## CRC-32C -/

/-- Castagnoli's polynomial, reflected (RFC 7143 §13.1). -/
def poly : UInt32 := 0x82F63B78

/-- One bit of the remainder shifted out. -/
def shift (c : UInt32) : UInt32 := if c &&& 1 == 1 then (c >>> 1) ^^^ poly else c >>> 1

/-- One byte into the remainder, a bit at a time. -/
def crcByte (c : UInt32) (b : Byte) : UInt32 :=
  let c := c ^^^ b.toNat.toUInt32
  shift (shift (shift (shift (shift (shift (shift (shift c)))))))

/-- The CRC-32C of `bs`: the remainder starts with every bit set and ends inverted (RFC 7143
§13.1, appendix A.4). -/
def crc32c (bs : Bytes) : UInt32 := bs.foldl crcByte 0xFFFFFFFF ^^^ 0xFFFFFFFF

/-! ## Numbers in octets -/

/-- `v` in `k` octets, least significant first; what does not fit is dropped. -/
def le : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, v => BitVec.ofNat 8 (v % 256) :: le k (v / 256)

/-- The number octets hold, least significant first. -/
def readLE : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * readLE bs

theorem le_length (k v : Nat) : (le k v).length = k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [le, ih]

theorem readLE_le (k v : Nat) (h : v < 256 ^ k) : readLE (le k v) = v := by
  induction k generalizing v with
  | zero => simp at h; simp [le, readLE, h]
  | succ k ih =>
    have hd : v / 256 < 256 ^ k := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.pow_succ] using h
    simp only [le, readLE, ih _ hd, BitVec.toNat_ofNat]
    have : v % 256 % 2 ^ 8 = v % 256 := Nat.mod_eq_of_lt (by omega)
    rw [this]
    omega

/-- The first octets of a number read as no more than the number. -/
theorem readLE_take_le (k n v : Nat) : readLE ((le k v).take n) ≤ v := by
  induction k generalizing n v with
  | zero => simp [le, readLE]
  | succ k ih =>
    cases n with
    | zero => simp [readLE]
    | succ m =>
      have := ih m (v / 256)
      simp only [le, List.take_succ_cons, readLE, BitVec.toNat_ofNat]
      omega

theorem readLE_replicate (j : Nat) : readLE (List.replicate j 0) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, readLE, ih]; rfl

/-- Zeros after octets add nothing to the number they hold. -/
theorem readLE_zeros (xs : Bytes) (j : Nat) : readLE (xs ++ List.replicate j 0) = readLE xs := by
  induction xs with
  | nil => rw [List.nil_append, readLE_replicate]; rfl
  | cons x xs ih => simp only [List.cons_append, readLE, ih]

/-! ## Records -/

/-- A group an article goes to, by its name, with the number the article has there. -/
structure Group where
  name : Bytes
  number : Nat
  deriving DecidableEq

/-- The commit of an article. -/
structure Commit where
  seq : Nat
  messageId : Bytes
  groups : List Group
  headerSize : Nat
  fileSize : Nat
  fileCrc : Nat
  deriving DecidableEq

/-- A record of the journal: its format, carrying the key its tags are made with, the commit of an
article, or the start of a run of the store. -/
inductive Record
  | format (key : Bytes)
  | commit (c : Commit)
  | start
  deriving DecidableEq

def formatType : Nat := 1
def commitType : Nat := 2
def startType : Nat := 3

/-- The journal's name for itself. -/
def journalTitle : Bytes := ascii "dragons-net journal"

/-- The title and the version, one octet. -/
def magic : Bytes := journalTitle ++ [BitVec.ofNat 8 1]

/-- The octets of a key. -/
def keyLength : Nat := 16

def Group.encode (g : Group) : Bytes :=
  BitVec.ofNat 8 g.name.length :: g.name ++ le 4 g.number

def Commit.payload (c : Commit) : Bytes :=
  le 8 c.seq ++ (BitVec.ofNat 8 c.messageId.length :: c.messageId) ++
    (BitVec.ofNat 8 c.groups.length :: (c.groups.map Group.encode).flatten) ++
    le 4 c.headerSize ++ le 4 c.fileSize ++ le 4 c.fileCrc

/-- A commit a correct store writes and a frame can hold: a sequence number from 1; a message
identifier of 1 to 250 octets (RFC 5536 §3.1.3); 1 to 16 groups (0005), each named in 1 to 64
octets, no two alike, with an article number RFC 3977 §6 allows, 1 to 2,147,483,647; a header
section no larger than its file; and each other number in the width it is written in. -/
def Commit.ok (c : Commit) : Bool :=
  1 ≤ c.seq && c.seq < 2 ^ 64 && 1 ≤ c.messageId.length && c.messageId.length ≤ 250 &&
    1 ≤ c.groups.length && c.groups.length ≤ 16 &&
    c.groups.all (fun g => 1 ≤ g.name.length && g.name.length ≤ 64 && 1 ≤ g.number &&
      g.number < 2 ^ 31) &&
    (c.groups.map Group.name).Nodup && c.headerSize ≤ c.fileSize && c.fileSize < 2 ^ 32 &&
    c.fileCrc < 2 ^ 32

/-- The octet that ends every frame. An append cut short and filled with zeros, or with any
octets not ending in it, loses it; it is neither 0x00 nor 0xFF, which fill unwritten space. -/
def endMark : Byte := BitVec.ofNat 8 0xA5

/-- The octets before a payload: its length, the tag and the type. -/
def headerLength : Nat := 13

/-- The most octets a payload holds: that of the largest commit. -/
def maxPayload : Nat := 8 + (1 + 250) + (1 + 16 * (1 + 64 + 4)) + 4 + 4 + 4

/-- The largest frame, the most one append writes. -/
def maxFrame : Nat := headerLength + maxPayload + 1

/-- The format's frame, the only append a journal without records can have had cut short. -/
def firstFrame : Nat := headerLength + magic.length + keyLength + 1

/-- The tag of a frame at `offset` in the journal: SipHash-2-4 under the journal's key, of the
offset in eight octets, the type and the payload. -/
def tagOf (key : Bytes) (offset type : Nat) (payload : Bytes) : Nat :=
  (SipHash.tag key (le 8 offset ++ BitVec.ofNat 8 type :: payload)).toNat

def frame (key : Bytes) (offset type : Nat) (payload : Bytes) : Bytes :=
  le 4 payload.length ++ le 8 (tagOf key offset type payload) ++
    (BitVec.ofNat 8 type :: payload) ++ [endMark]

def Record.type : Record → Nat
  | .format _ => formatType
  | .commit _ => commitType
  | .start => startType

def Record.payload : Record → Bytes
  | .format key => magic ++ key
  | .commit c => c.payload
  | .start => []

/-- The key a record carries: the format's. -/
def Record.key : Record → Option Bytes
  | .format key => some key
  | _ => none

/-- A record framed at `offset` in a journal keyed with `key`. -/
def Record.encode (key : Bytes) (offset : Nat) (r : Record) : Bytes :=
  frame key offset r.type r.payload

/-- Records framed one after the other from `offset`, each at the place it lands. -/
def encodeFrom (key : Bytes) : Nat → List Record → Bytes
  | _, [] => []
  | offset, r :: rs =>
    r.encode key offset ++ encodeFrom key (offset + (r.encode key offset).length) rs

/-- A journal: its format, carrying `key`, then the records `rs`. -/
def journal (key : Bytes) (rs : List Record) : Bytes := encodeFrom key 0 (.format key :: rs)

/-! ## Reading records -/

/-- `k` octets as a number and what follows them, if there are `k`. -/
def takeLE (k : Nat) (bs : Bytes) : Option (Nat × Bytes) :=
  if k ≤ bs.length then some (readLE (bs.take k), bs.drop k) else none

/-- A length octet and that many octets after it. -/
def takeCounted (bs : Bytes) : Option (Bytes × Bytes) :=
  match bs with
  | n :: rest => if n.toNat ≤ rest.length then some (rest.take n.toNat, rest.drop n.toNat) else none
  | [] => none

def takeGroup (bs : Bytes) : Option (Group × Bytes) := do
  let (name, bs) ← takeCounted bs
  let (number, bs) ← takeLE 4 bs
  pure (⟨name, number⟩, bs)

def takeGroups : Nat → Bytes → Option (List Group × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (g, bs) ← takeGroup bs
    let (gs, bs) ← takeGroups n bs
    pure (g :: gs, bs)

/-- The commit a payload holds, if it holds exactly one that a correct store writes; with `exact`
false, octets after it are let be, and with `checked` false, any commit is taken. -/
def decodeCommit (bs : Bytes) (exact : Bool := true) (checked : Bool := true) : Option Commit := do
  let (seq, bs) ← takeLE 8 bs
  let (messageId, bs) ← takeCounted bs
  let (count, bs) ← match bs with
    | n :: rest => some (n.toNat, rest)
    | [] => none
  let (groups, bs) ← takeGroups count bs
  let (headerSize, bs) ← takeLE 4 bs
  let (fileSize, bs) ← takeLE 4 bs
  let (fileCrc, bs) ← takeLE 4 bs
  let c : Commit := ⟨seq, messageId, groups, headerSize, fileSize, fileCrc⟩
  if (bs.isEmpty || !exact) && (c.ok || !checked) then some c else none

/-- Why a frame is not a record. -/
inductive Why
  /-- fewer octets than its header, or than its length says -/
  | short
  /-- its length is more than any payload's -/
  | tooLong
  /-- its last octet is not the end mark -/
  | unterminated
  /-- its tag is not the one its key makes, or no key checks it -/
  | tag
  /-- it checks, but is no record the journal holds -/
  | notARecord
  /-- a second format record -/
  | formatAgain
  deriving DecidableEq

/-- Whether an append the crash cut short can leave a frame that fails so. -/
def Why.torn : Why → Bool
  | .short | .tooLong | .unterminated | .tag => true
  | _ => false

/-- What the octets at a place in the journal are. -/
inductive Next
  /-- nothing more -/
  | done
  /-- a record, the octets it took, and what follows it -/
  | record (r : Record) (taken : Nat) (rest : Bytes)
  /-- a frame that does not check -/
  | bad (why : Why)
  deriving DecidableEq

/-- The rules of reading that a version of them can change, each a field so that one with it
changed can show it matters. -/
structure Rules where
  /-- the longest payload a length may give -/
  maxPayload : Nat := maxPayload
  /-- the longest tail taken for a torn append once a record has been read -/
  maxFrame : Nat := maxFrame
  /-- the longest tail taken for a torn append before any record -/
  firstFrame : Nat := firstFrame
  /-- whether the end mark is checked -/
  ended : Bool := true
  /-- whether the tag is checked -/
  tagged : Bool := true
  /-- whether the format may appear only once -/
  formatOnce : Bool := true
  /-- whether a commit has to take its whole payload -/
  exact : Bool := true
  /-- whether a commit has to be one a correct store writes -/
  checked : Bool := true
  /-- whether only a frame a torn append can leave may be a torn tail -/
  strict : Bool := true
  /-- whether a torn tail may hold no frame that checks after its first octet -/
  quiet : Bool := true
  /-- whether only a frame of the format's shape carries a key -/
  shaped : Bool := true

def spec : Rules := {}

@[simp] theorem spec_maxPayload : spec.maxPayload = maxPayload := rfl
@[simp] theorem spec_maxFrame : spec.maxFrame = maxFrame := rfl
@[simp] theorem spec_firstFrame : spec.firstFrame = firstFrame := rfl
@[simp] theorem spec_ended : spec.ended = true := rfl
@[simp] theorem spec_tagged : spec.tagged = true := rfl
@[simp] theorem spec_formatOnce : spec.formatOnce = true := rfl
@[simp] theorem spec_strict : spec.strict = true := rfl
@[simp] theorem spec_quiet : spec.quiet = true := rfl
@[simp] theorem spec_shaped : spec.shaped = true := rfl

/-- The key a frame carries the way the format does: type 1 and a payload of the journal's title,
a version and a key; with `shaped` false, the last sixteen octets of any payload. A journal's first
frame is checked with the key it carries. -/
def keyIn (r : Rules) (type : Nat) (payload : Bytes) : Option Bytes :=
  if !r.shaped then
    if keyLength ≤ payload.length then some (payload.drop (payload.length - keyLength)) else none
  else if type == formatType && payload.length == magic.length + keyLength &&
      payload.take journalTitle.length == journalTitle then some (payload.drop magic.length)
  else none

/-- The record a type and payload make, if they make one. -/
def recordOf (r : Rules) (type : Nat) (payload : Bytes) : Option Record :=
  if type == formatType then
    if payload.length == magic.length + keyLength && payload.take magic.length == magic then
      some (.format (payload.drop magic.length))
    else none
  else if type == commitType then
    (decodeCommit payload r.exact r.checked).map .commit
  else if type == startType then
    if payload.isEmpty then some .start else none
  else none

/-- Whether a stored tag is not the one a key makes; with no key, a tag cannot be checked. -/
def tagWrong : Option Bytes → Nat → Nat → Nat → Bytes → Bool
  | some key, stored, offset, type, payload => stored != tagOf key offset type payload
  | none, _, _, _, _ => true

/-- Whether `bs` holds at least `n` octets, looking at no more than `n` of them. -/
def atLeast : Nat → Bytes → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, _ :: bs => atLeast n bs

/-- The frame at `offset`, the start of `bs`; `key` is the journal's once its format has been read.
The end mark is checked before the tag, so that a frame cut short and filled is known without it. -/
def next (r : Rules) (key : Option Bytes) (offset : Nat) (bs : Bytes) : Next :=
  if bs.isEmpty then .done
  else if !atLeast headerLength bs then .bad .short
  else
    let len := readLE (bs.take 4)
    if len > r.maxPayload then .bad .tooLong
    else if !atLeast (headerLength + len + 1) bs then .bad .short
    else if r.ended && bs.getD (headerLength + len) 0 != endMark then .bad .unterminated
    else
      match (bs.drop 12).take (1 + len) with
      | t :: payload =>
        if r.tagged && tagWrong (key <|> keyIn r t.toNat payload) (readLE ((bs.drop 4).take 8))
            offset t.toNat payload then .bad .tag
        else
          match recordOf r t.toNat payload with
          | some rec => .record rec (headerLength + len + 1) (bs.drop (headerLength + len + 1))
          | none => .bad .notARecord
      | [] => .bad .notARecord

/-- How a journal ends. -/
inductive End
  | clean
  /-- a torn tail at this offset, to be truncated away -/
  | torn (at_ : Nat)
  /-- corruption at this offset -/
  | corrupt (at_ : Nat) (why : Why)
  deriving DecidableEq

structure Scan where
  records : List Record
  ending : End
  deriving DecidableEq

/-- Whether the octets at `offset`, the start of `bs`, are a whole frame whose tag `key` makes. -/
def checks (r : Rules) (key : Bytes) (offset : Nat) (bs : Bytes) : Bool :=
  match next r (some key) offset bs with
  | .record .. | .bad .notARecord => true
  | _ => false

/-- Whether a frame whose tag `key` makes starts anywhere in `bs`, which lies at `offset`. -/
def anyChecks (r : Rules) (key : Bytes) : Nat → Bytes → Bool
  | _, [] => false
  | offset, b :: rest => checks r key offset (b :: rest) || anyChecks r key (offset + 1) rest

/-- Whether reading that stops at `offset`, the start of `bs`, `key` the journal's once its format
has been read stops in a torn tail: if a torn append can leave the frame, `bs` fits the append that
can have been cut — the format's before the format, the largest frame after — and no frame that
checks starts in it after its first octet, as none does after the last thing written. -/
def tornHere (r : Rules) (offset : Nat) (bs : Bytes) (key : Option Bytes) (why : Why) : Bool :=
  (why.torn || !r.strict) && bs.length ≤ (if key.isSome then r.maxFrame else r.firstFrame) &&
    !(r.quiet && key.any fun k => anyChecks r k (offset + 1) bs.tail)

/-- What stops reading at `offset`: a torn tail where `tornHere` says so, corruption otherwise. -/
def stop (r : Rules) (offset : Nat) (bs : Bytes) (key : Option Bytes) (why : Why) : End :=
  if tornHere r offset bs key why then .torn offset else .corrupt offset why

theorem stop_cases (r : Rules) (offset : Nat) (bs : Bytes) (key : Option Bytes) (why : Why) :
    stop r offset bs key why = .torn offset ∨ stop r offset bs key why = .corrupt offset why := by
  unfold stop
  cases tornHere r offset bs key why <;> simp

/-- Reading from `offset` with the journal's `key` once known, `fuel` records at most; each record
takes more than `headerLength` octets, so `scanWith` gives fuel enough and the first case is never
met. A journal's first record is its format: no other frame can be checked before its key. -/
def scanFrom (r : Rules) : Nat → Bytes → Nat → Option Bytes → List Record → Scan
  | 0, _, offset, _, acc => ⟨acc.reverse, .corrupt offset .tooLong⟩
  | fuel + 1, bs, offset, key, acc =>
    match next r key offset bs with
    | .done => ⟨acc.reverse, .clean⟩
    | .bad why => ⟨acc.reverse, stop r offset bs key why⟩
    | .record rec taken rest =>
      if r.formatOnce && !acc.isEmpty && rec.key.isSome then
        ⟨acc.reverse, .corrupt offset .formatAgain⟩
      else scanFrom r fuel rest (offset + taken) (key <|> rec.key) (rec :: acc)

/-- **How a journal reads back**, under rules `r`. Each record takes more than `headerLength`
octets, so the length of the journal is fuel enough. -/
def scanWith (r : Rules) (bs : Bytes) : Scan := scanFrom r (bs.length + 1) bs 0 none []

def scan : Bytes → Scan := scanWith spec

/-! ## Names -/

def hexDigit (n : Nat) : Byte := BitVec.ofNat 8 (if n < 10 then 48 + n else 87 + n)

/-- The last `k` hexadecimal digits of `n`, most significant first. -/
def hexOf : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => hexDigit (n / 16 ^ k % 16) :: hexOf k n

/-- `n` in sixteen hexadecimal digits, most significant first. -/
def hex16 (n : Nat) : Bytes := hexOf 16 n

def journalName : Bytes := ascii "journal"
def finalName (seq : Nat) : Bytes := ascii "a" ++ hex16 seq
def tempName (seq : Nat) : Bytes := ascii "t" ++ hex16 seq
/-- An article's file set aside by recovery. -/
def quarantineName (seq : Nat) : Bytes := ascii "q" ++ hex16 seq
/-- The octets recovery truncated from the journal, kept under a number of the store's. -/
def tailName (seq : Nat) : Bytes := ascii "j" ++ hex16 seq

/-- A name the store gives a file. -/
inductive Name
  | journal
  | final (seq : Nat)
  | temp (seq : Nat)
  | quarantine (seq : Nat)
  | tail (seq : Nat)
  deriving DecidableEq

/-- The name a file of the store has. -/
def Name.bytes : Name → Bytes
  | .journal => journalName
  | .final s => finalName s
  | .temp s => tempName s
  | .quarantine s => quarantineName s
  | .tail s => tailName s

/-- Whether a name's number fits its sixteen digits. -/
def Name.valid : Name → Bool
  | .journal => true
  | .final s | .temp s | .quarantine s | .tail s => s < 2 ^ 64

def digitValue (b : Byte) : Option Nat :=
  if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b.toNat ∧ b.toNat ≤ 102 then some (b.toNat - 87)
  else none

/-- One more hexadecimal digit after the number `m`. -/
def hexStep (m : Nat) (d : Byte) : Option Nat := (digitValue d).map (16 * m + ·)

/-- The number sixteen lowercase hexadecimal digits write. -/
def hexValue (ds : Bytes) : Option Nat :=
  if ds.length = 16 then ds.foldlM hexStep 0 else none

/-- The file a name is, if the store gives names of its shape: any other name in the spool
directory makes the store corrupt (0005). -/
def parseName (n : Bytes) : Option Name :=
  if n == journalName then some .journal
  else
    match n with
    | k :: ds =>
      if k == (ascii "a").headD 0 then .final <$> hexValue ds
      else if k == (ascii "t").headD 0 then .temp <$> hexValue ds
      else if k == (ascii "q").headD 0 then .quarantine <$> hexValue ds
      else if k == (ascii "j").headD 0 then .tail <$> hexValue ds
      else none
    | [] => none

/-! ## What is proven of records -/

theorem take_le (k v : Nat) : (le k v).take k = le k v :=
  List.take_of_length_le (by simp [le_length])

theorem takeLE_le (k v : Nat) (rest : Bytes) (h : v < 256 ^ k) :
    takeLE k (le k v ++ rest) = some (v, rest) := by
  simp [takeLE, le_length, readLE_le _ _ h, List.take_left', List.drop_left']

theorem takeCounted_enc (bs rest : Bytes) (h : bs.length < 256) :
    takeCounted (BitVec.ofNat 8 bs.length :: (bs ++ rest)) = some (bs, rest) := by
  have : bs.length % 2 ^ 8 = bs.length := Nat.mod_eq_of_lt (by omega)
  simp [takeCounted, BitVec.toNat_ofNat, this, List.take_left', List.drop_left']

theorem takeGroup_enc (g : Group) (rest : Bytes) (hn : g.name.length < 256)
    (hv : g.number < 2 ^ 32) : takeGroup (g.encode ++ rest) = some (g, rest) := by
  have hv' : g.number < 256 ^ 4 := by simpa using hv
  simp only [takeGroup, Group.encode, List.cons_append, List.append_assoc,
    takeCounted_enc _ _ hn, takeLE_le _ _ _ hv', Option.bind_eq_bind, Option.bind_some]
  rfl

theorem takeGroups_enc (gs : List Group) (rest : Bytes)
    (h : ∀ g ∈ gs, g.name.length < 256 ∧ g.number < 2 ^ 32) :
    takeGroups gs.length ((gs.map Group.encode).flatten ++ rest) = some (gs, rest) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [takeGroups, List.map_cons, List.flatten_cons, List.append_assoc,
      takeGroup_enc g _ hg.1 hg.2, Option.bind_eq_bind, Option.bind_some, ht]
    rfl

/-- **A commit decodes to itself** from its payload, when a correct store writes it. -/
theorem decode_payload (c : Commit) (h : c.ok = true) : decodeCommit c.payload = some c := by
  have hall := h
  simp only [Commit.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hs⟩, hm1⟩, hm2⟩, hg1⟩, hg2⟩, hgs⟩, _⟩, hh⟩, hf⟩, hc⟩ := h
  have hgs' : ∀ g ∈ c.groups, g.name.length < 256 ∧ g.number < 2 ^ 32 := by
    intro g hg
    have := hgs g hg
    omega
  have hs' : c.seq < 256 ^ 8 := by simpa using hs
  have hf' : c.fileSize < 256 ^ 4 := by simpa using hf
  have hh' : c.headerSize < 256 ^ 4 := Nat.lt_of_le_of_lt hh hf'
  have hc' : c.fileCrc < 256 ^ 4 := by simpa using hc
  have hcount : c.groups.length % 2 ^ 8 = c.groups.length := Nat.mod_eq_of_lt (by omega)
  simp only [decodeCommit, Commit.payload, List.cons_append, List.append_assoc,
    takeLE_le _ _ _ hs', takeCounted_enc c.messageId _ (by omega), Option.bind_eq_bind,
    Option.bind_some,
    BitVec.toNat_ofNat, hcount, takeGroups_enc _ _ hgs']
  simp [takeLE, le_length, take_le, readLE_le _ _ hh', readLE_le _ _ hf', readLE_le _ _ hc',
    List.take_left', List.drop_left', hall]

def Record.ok : Record → Bool
  | .format key => key.length == keyLength
  | .commit c => c.ok
  | .start => true

theorem magic_length : magic.length = 20 := by decide

theorem type_toNat (r : Record) : (BitVec.ofNat 8 r.type).toNat = r.type := by
  cases r <;> rfl

theorem groups_length (gs : List Group) (h : ∀ g ∈ gs, g.name.length ≤ 64) :
    ((gs.map Group.encode).flatten).length ≤ 69 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.flatten_cons, List.length_append, Group.encode,
      List.length_cons, le_length, List.length_cons]
    omega

theorem payload_length (r : Record) (h : r.ok = true) : r.payload.length ≤ maxPayload := by
  cases r with
  | format key =>
    simp only [Record.ok, beq_iff_eq, keyLength] at h
    simp only [Record.payload, List.length_append, magic_length, h, maxPayload]
    omega
  | commit c =>
    simp only [Record.ok, Commit.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hm2⟩, _⟩, hg2⟩, hgs⟩, _⟩, _⟩, _⟩, _⟩ := h
    have := groups_length c.groups (fun g hg => by have := hgs g hg; omega)
    simp only [Record.payload, Commit.payload, List.length_append, List.length_cons, le_length,
      maxPayload]
    omega
  | start => simp [Record.payload]

theorem encode_length (r : Record) (key : Bytes) (offset : Nat) :
    (r.encode key offset).length = headerLength + r.payload.length + 1 := by
  simp [Record.encode, frame, le_length, headerLength]
  omega

/-- **The start's frame is the shortest**: every other record's is longer, whatever the keys and
offsets, so an append of a start never leaves another record's frame whole. -/
theorem start_shortest (r : Record) (hr : r ≠ .start) (k k' : Bytes) (o o' : Nat) :
    (Record.start.encode k o).length < (r.encode k' o').length := by
  rw [encode_length, encode_length]
  cases r with
  | format key => simp [Record.payload, magic_length]; omega
  | commit c => simp [Record.payload, Commit.payload, le_length]; omega
  | start => exact absurd rfl hr

theorem encode_le (r : Record) (h : r.ok = true) (key : Bytes) (offset : Nat) :
    (r.encode key offset).length ≤ maxFrame := by
  have := payload_length r h
  rw [encode_length]
  simp only [maxFrame]
  omega

theorem format_encode_length (key : Bytes) (h : key.length = keyLength) (offset : Nat) :
    ((Record.format key).encode key offset).length = firstFrame := by
  rw [encode_length]
  simp only [Record.payload, List.length_append, h, firstFrame]
  omega

/-- A frame laid out as reading takes it apart. -/
theorem encode_shape (r : Record) (key : Bytes) (offset : Nat) (rest : Bytes) :
    r.encode key offset ++ rest =
      (le 4 r.payload.length ++ le 8 (tagOf key offset r.type r.payload)) ++
        (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest)) := by
  simp [Record.encode, frame]

theorem recordOf_payload (r : Record) (h : r.ok = true) :
    recordOf spec r.type r.payload = some r := by
  cases r with
  | format key =>
    simp only [Record.ok, beq_iff_eq] at h
    have ht : (magic ++ key).take magic.length = magic := List.take_left' rfl
    have hd : (magic ++ key).drop magic.length = key := List.drop_left' rfl
    simp [recordOf, Record.type, Record.payload, formatType, ht, hd, h]
  | commit c =>
    have hd := decode_payload c h
    simp [recordOf, Record.type, Record.payload, formatType, commitType, spec, hd]
  | start => simp [recordOf, Record.type, Record.payload, formatType, commitType, startType]

/-- A format record carries its key the way reading looks for one. -/
theorem keyIn_format (key : Bytes) (h : key.length = keyLength) :
    keyIn spec formatType (magic ++ key) = some key := by
  have ht : (magic ++ key).take journalTitle.length = journalTitle := by
    rw [magic, List.append_assoc]; exact List.take_left' rfl
  simp only [keyLength] at h
  simp [keyIn, ht, magic_length, keyLength, h]

theorem tag_lt (key : Bytes) (offset type : Nat) (payload : Bytes) :
    tagOf key offset type payload < 256 ^ 8 := by
  have := UInt64.toNat_lt (SipHash.tag key (le 8 offset ++ BitVec.ofNat 8 type :: payload))
  simp only [tagOf]
  omega

theorem atLeast_eq (n : Nat) (bs : Bytes) : atLeast n bs = decide (n ≤ bs.length) := by
  induction n generalizing bs with
  | zero => simp [atLeast]
  | succ n ih => cases bs <;> simp [atLeast, ih]

theorem atLeast_of_le (n : Nat) (bs : Bytes) (h : n ≤ bs.length) : atLeast n bs = true := by
  simp [atLeast_eq, h]

theorem atLeast_of_lt (n : Nat) (bs : Bytes) (h : bs.length < n) : atLeast n bs = false := by
  simp [atLeast_eq]; omega

theorem isEmpty_of_length (bs : Bytes) (h : 0 < bs.length) : bs.isEmpty = false := by
  cases bs with
  | nil => simp at h
  | cons _ _ => rfl

/-- **A record reads back as itself**, whatever follows it, when the key reading checks it with
is the one it was framed with. -/
theorem next_encode (r : Record) (h : r.ok = true) (key : Option Bytes) (k : Bytes)
    (hk : (key <|> keyIn spec r.type r.payload) = some k) (offset : Nat) (rest : Bytes) :
    next spec key offset (r.encode k offset ++ rest) =
      .record r (r.encode k offset).length rest := by
  have hp := payload_length r h
  have hlen : r.payload.length < 256 ^ 4 := by simp only [maxPayload] at hp; omega
  have htag := tag_lt k offset r.type r.payload
  have hab : (le 4 r.payload.length ++ le 8 (tagOf k offset r.type r.payload)).length = 12 := by
    simp [le_length]
  have h4 : ((le 4 r.payload.length ++ le 8 (tagOf k offset r.type r.payload)) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).take 4 =
      le 4 r.payload.length := by
    rw [List.append_assoc]; exact List.take_left' (le_length _ _)
  have h48 : (((le 4 r.payload.length ++ le 8 (tagOf k offset r.type r.payload)) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).drop 4).take 8 =
      le 8 (tagOf k offset r.type r.payload) := by
    rw [List.append_assoc, List.drop_left' (le_length _ _)]; exact List.take_left' (le_length _ _)
  have hbody : (((le 4 r.payload.length ++ le 8 (tagOf k offset r.type r.payload)) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).drop 12).take
        (1 + r.payload.length) = BitVec.ofNat 8 r.type :: r.payload := by
    rw [List.drop_left' hab, Nat.add_comm, List.take_succ_cons, List.take_left' rfl]
  have hend : ((le 4 r.payload.length ++ le 8 (tagOf k offset r.type r.payload)) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).getD
        (headerLength + r.payload.length) 0 = endMark := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hab]; simp only [headerLength]; omega), hab,
      show headerLength + r.payload.length - 12 = r.payload.length + 1 by
        simp only [headerLength]; omega]
    simp
  have hrest : ((le 4 r.payload.length ++ le 8 (tagOf k offset r.type r.payload)) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).drop
        (headerLength + r.payload.length + 1) = rest := by
    rw [show headerLength + r.payload.length + 1 = 12 + (r.payload.length + 2) by
      simp only [headerLength]; omega, ← List.drop_drop, List.drop_left' hab]
    simp
  have hfull : ((le 4 r.payload.length ++ le 8 (tagOf k offset r.type r.payload)) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).length =
      headerLength + r.payload.length + 1 + rest.length := by
    simp [le_length, headerLength]; omega
  have hr := recordOf_payload r h
  have hw : tagWrong (key <|> keyIn spec r.type r.payload) (tagOf k offset r.type r.payload)
      offset r.type r.payload = false := by
    rw [hk]; simp [tagWrong]
  rw [encode_shape, encode_length]
  generalize (le 4 r.payload.length ++ le 8 (tagOf k offset r.type r.payload)) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest)) = bs
    at h4 h48 hbody hend hrest hfull
  have c1 := isEmpty_of_length bs (by rw [hfull]; omega)
  have c2 := atLeast_of_le headerLength bs (by rw [hfull]; omega)
  have c3 := atLeast_of_le (headerLength + r.payload.length + 1) bs (by rw [hfull]; omega)
  have c4 : ¬ (r.payload.length > maxPayload) := by omega
  unfold next
  simp only [h4, readLE_le _ _ hlen, c1, c2, c3, c4, spec_maxPayload, spec_ended, spec_tagged, hend,
    bne_self_eq_false, Bool.and_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hbody, h48,
    readLE_le _ _ htag, type_toNat, hw, hr, hrest]

theorem encodeFrom_cons (key : Bytes) (offset : Nat) (r : Record) (rs : List Record) :
    encodeFrom key offset (r :: rs) =
      r.encode key offset ++ encodeFrom key (offset + (r.encode key offset).length) rs := rfl

theorem encodeFrom_length (key : Bytes) (rs : List Record) :
    ∀ offset, headerLength * rs.length ≤ (encodeFrom key offset rs).length := by
  induction rs with
  | nil => intro offset; simp [encodeFrom]
  | cons r rs ih =>
    intro offset
    have := ih (offset + (r.encode key offset).length)
    have h2 := encode_length r key offset
    rw [encodeFrom_cons, List.length_append, List.length_cons]
    simp only [Nat.mul_succ]
    omega

/-- The records a journal holds after its format: records a correct store writes that carry no
key, its commits and starts. -/
def Appends (cs : List Record) : Prop := ∀ r ∈ cs, r.ok = true ∧ r.key = none

/-- Reading on through what follows the format, once its key is known. -/
theorem scanFrom_appends (k : Bytes) (cs : List Record) (hcs : Appends cs) :
    ∀ (fuel : Nat) (tail : Bytes) (off : Nat) (acc : List Record), cs.length < fuel → acc ≠ [] →
      scanFrom spec fuel (encodeFrom k off cs ++ tail) off (some k) acc =
        scanFrom spec (fuel - cs.length) tail (off + (encodeFrom k off cs).length) (some k)
          (cs.reverse ++ acc) := by
  induction cs with
  | nil => intro fuel tail off acc _ _; simp [encodeFrom]
  | cons c cs ih =>
    intro fuel tail off acc hf hacc
    have hc := hcs c (by simp)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    rw [encodeFrom_cons, List.append_assoc]
    simp only [scanFrom, next_encode c hc.1 (some k) k rfl]
    have hne : acc.isEmpty = false := by cases acc <;> simp_all
    simp only [spec_formatOnce, hne, hc.2, Option.isSome_none, Bool.and_false, Bool.not_false,
      Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    rw [show (some k <|> (none : Option Bytes)) = some k from rfl]
    rw [ih (fun r hr => hcs r (by simp [hr])) f tail (off + (c.encode k off).length) (c :: acc)
      (by simp at hf; omega) (by simp)]
    have e1 : f + 1 - (c :: cs).length = f - cs.length := by simp
    have e2 : off + (c.encode k off ++ encodeFrom k (off + (c.encode k off).length) cs).length =
        off + (c.encode k off).length +
          (encodeFrom k (off + (c.encode k off).length) cs).length := by simp; omega
    have e3 : (c :: cs).reverse ++ acc = cs.reverse ++ c :: acc := by simp
    rw [e1, e2, e3]

/-- Reading on after a frame that reads as a format carrying `k`, then records framed under `k`:
what follows them is read with the format and the records taken. -/
theorem scan_after_format (F k : Bytes) (h0 : 0 < F.length)
    (hF : ∀ rest, next spec none 0 (F ++ rest) = .record (.format k) F.length rest)
    (cs : List Record) (hcs : Appends cs) (tail : Bytes) :
    ∃ g, scan (F ++ (encodeFrom k F.length cs ++ tail)) =
      scanFrom spec (g + 1) tail (F.length + (encodeFrom k F.length cs).length) (some k)
        (cs.reverse ++ [.format k]) := by
  have hlen := encodeFrom_length k cs F.length
  simp only [headerLength] at hlen
  obtain ⟨f, hfe⟩ : ∃ f, (F ++ (encodeFrom k F.length cs ++ tail)).length + 1 = f + 1 :=
    ⟨_, rfl⟩
  have hl : (F ++ (encodeFrom k F.length cs ++ tail)).length =
      F.length + (encodeFrom k F.length cs).length + tail.length := by
    simp only [List.length_append]; omega
  obtain ⟨g, hg⟩ : ∃ g, f - cs.length = g + 1 := ⟨f - cs.length - 1, by omega⟩
  refine ⟨g, ?_⟩
  rw [← hg]
  calc scan (F ++ (encodeFrom k F.length cs ++ tail))
      = scanFrom spec (f + 1) (F ++ (encodeFrom k F.length cs ++ tail)) 0 none [] := by
        simp only [scan, scanWith]; rw [hfe]
    _ = scanFrom spec f (encodeFrom k F.length cs ++ tail) (0 + F.length) (some k)
          [.format k] := by
        simp only [scanFrom, hF, spec_formatOnce, List.isEmpty_nil, Bool.not_true,
          Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
        rfl
    _ = scanFrom spec (f - cs.length) tail (0 + F.length + (encodeFrom k F.length cs).length)
          (some k) (cs.reverse ++ [.format k]) := by
        rw [Nat.zero_add]
        exact scanFrom_appends k cs hcs f tail F.length [.format k] (by omega) (by simp)
    _ = _ := by rw [Nat.zero_add]

/-- The format's frame reads as the format, its tag checked with the key it carries. -/
theorem next_format (k : Bytes) (hk : k.length = keyLength) (rest : Bytes) :
    next spec none 0 ((Record.format k).encode k 0 ++ rest) =
      .record (.format k) ((Record.format k).encode k 0).length rest :=
  next_encode (.format k) (by simp [Record.ok, hk]) none k
    (by simp only [Record.type, Record.payload]; rw [keyIn_format k hk]; rfl) 0 rest

theorem journal_split (k : Bytes) (cs : List Record) :
    journal k cs = (Record.format k).encode k 0 ++
      encodeFrom k ((Record.format k).encode k 0).length cs := by
  simp [journal, encodeFrom]

/-- **A journal of records reads back as those records**, ending cleanly: its format, then its
commits and starts. -/
theorem scan_encoded (k : Bytes) (hk : k.length = keyLength) (cs : List Record)
    (hcs : Appends cs) : scan (journal k cs) = ⟨.format k :: cs, .clean⟩ := by
  obtain ⟨g, hg⟩ := scan_after_format ((Record.format k).encode k 0) k
    (by rw [format_encode_length k hk]; decide) (next_format k hk) cs hcs []
  rw [List.append_nil] at hg
  rw [journal_split, hg]
  simp [scanFrom, next]

/-- No frame whose tag `k` makes starts in `t`, which lies at `offset`, after its first octet: what
an append the crash cut short leaves, since that tag takes the key. -/
def Quiet (k : Bytes) (offset : Nat) (t : Bytes) : Prop :=
  anyChecks spec k (offset + 1) t.tail = false

/-- After the records, a frame `t` starts with that fails at `w`: what `stop` makes of it. -/
theorem scan_stop_with (k : Bytes) (hk : k.length = keyLength) (cs : List Record)
    (hcs : Appends cs) (t : Bytes) (w : Why)
    (hw : next spec (some k) (journal k cs).length t = .bad w) :
    scan (journal k cs ++ t) = ⟨.format k :: cs, stop spec (journal k cs).length t (some k) w⟩ := by
  obtain ⟨g, hg⟩ := scan_after_format ((Record.format k).encode k 0) k
    (by rw [format_encode_length k hk]; decide) (next_format k hk) cs hcs t
  have hj : (journal k cs).length = ((Record.format k).encode k 0).length +
      (encodeFrom k ((Record.format k).encode k 0).length cs).length := by
    rw [journal_split, List.length_append]
  have hs : scan (journal k cs ++ t) = scanFrom spec (g + 1) t
      (((Record.format k).encode k 0).length +
        (encodeFrom k ((Record.format k).encode k 0).length cs).length) (some k)
      (cs.reverse ++ [.format k]) := by
    rw [journal_split, List.append_assoc, hg]
  rw [hs, hj]
  rw [hj] at hw
  simp only [scanFrom, hw, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.reverse_reverse, List.singleton_append]

/-- After the records, what does not check for a reason a torn append can leave, is no longer
than the largest frame and is quiet reads as a torn tail where it starts. -/
theorem scan_stop (k : Bytes) (hk : k.length = keyLength) (cs : List Record) (hcs : Appends cs)
    (t : Bytes) (w : Why) (hw : next spec (some k) (journal k cs).length t = .bad w)
    (hwt : w.torn = true) (ht : t.length ≤ maxFrame) (hq : Quiet k (journal k cs).length t) :
    scan (journal k cs ++ t) = ⟨.format k :: cs, .torn (journal k cs).length⟩ := by
  rw [scan_stop_with k hk cs hcs t w hw]
  simp only [Quiet] at hq
  simp [stop, tornHere, hwt, ht, hq]

/-- Before any record, what does not check for a reason a torn append can leave, and is no longer
than the format's frame, reads as a torn tail at the start. -/
theorem scan_stop_first (t : Bytes) (w : Why) (hw : next spec none 0 t = .bad w)
    (hwt : w.torn = true) (ht : t.length ≤ firstFrame) : scan t = ⟨[], .torn 0⟩ := by
  simp only [scan, scanWith]
  obtain ⟨f, hfe⟩ : ∃ f, t.length + 1 = f + 1 := ⟨_, rfl⟩
  rw [hfe]
  simp only [scanFrom, hw]
  simp [stop, tornHere, hwt, ht]

/-- A record framed where it lies, anywhere in what follows `xs`, is a frame that checks. -/
theorem anyChecks_encode (k : Bytes) (r : Record) (hr : r.ok = true) (rest : Bytes) :
    ∀ (xs : Bytes) (offset : Nat),
      anyChecks spec k offset (xs ++ r.encode k (offset + xs.length) ++ rest) = true := by
  intro xs
  induction xs with
  | nil =>
    intro offset
    have hc : checks spec k offset (r.encode k offset ++ rest) = true := by
      simp [checks, next_encode r hr (some k) k rfl offset rest]
    have hl : 0 < (r.encode k offset ++ rest).length := by
      rw [List.length_append, encode_length]; omega
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    revert hc hl
    cases r.encode k offset ++ rest with
    | nil => simp
    | cons b bs => intro hc _; simp [anyChecks, hc]
  | cons x xs ih =>
    intro offset
    have := ih (offset + 1)
    rw [show offset + 1 + xs.length = offset + (x :: xs).length by simp; omega] at this
    show anyChecks spec k offset
      (x :: (xs ++ r.encode k (offset + (x :: xs).length) ++ rest)) = true
    simp only [anyChecks, this, Bool.or_true]

/-- **Damage before the last record is corruption**: after the records, a frame that does not
check, followed after its first octet by a record framed where it lies, is not a torn tail — an
append the crash cut short is the last thing written. -/
theorem scan_damaged (k : Bytes) (hk : k.length = keyLength) (cs : List Record)
    (hcs : Appends cs) (x : Byte) (xs : Bytes) (r : Record) (hr : r.ok = true) (rest : Bytes)
    (w : Why) (hw : next spec (some k) (journal k cs).length
      (x :: (xs ++ r.encode k ((journal k cs).length + 1 + xs.length) ++ rest)) = .bad w) :
    scan (journal k cs ++ x :: (xs ++ r.encode k ((journal k cs).length + 1 + xs.length) ++ rest)) =
      ⟨.format k :: cs, .corrupt (journal k cs).length w⟩ := by
  rw [scan_stop_with k hk cs hcs _ w hw]
  have hl := anyChecks_encode k r hr rest xs ((journal k cs).length + 1)
  simp only [stop, tornHere, List.tail_cons, Option.isSome_some, Option.any_some, hl, spec_quiet,
    Bool.and_true, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- A proper prefix of a frame is short: its length says more than there is. -/
theorem next_short (r : Record) (h : r.ok = true) (k : Bytes) (o : Nat) (key : Option Bytes)
    (offset n : Nat) (h0 : 0 < n) (hn : n < (r.encode k o).length) :
    next spec key offset ((r.encode k o).take n) = .bad .short := by
  have hp := payload_length r h
  have hlen : r.payload.length < 256 ^ 4 := by simp only [maxPayload] at hp; omega
  have hl := encode_length r k o
  have htl : ((r.encode k o).take n).length = n := by simp [List.length_take]; omega
  have hA : (r.encode k o).take 4 = le 4 r.payload.length := by
    simp [Record.encode, frame, List.take_left', le_length]
  have c1 := isEmpty_of_length ((r.encode k o).take n) (by rw [htl]; exact h0)
  unfold next
  by_cases h9 : n < headerLength
  · have c2 := atLeast_of_lt headerLength ((r.encode k o).take n) (by rw [htl]; exact h9)
    simp only [c1, c2, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  · have c2 := atLeast_of_le headerLength ((r.encode k o).take n) (by rw [htl]; omega)
    have h4 : ((r.encode k o).take n).take 4 = le 4 r.payload.length := by
      rw [List.take_take, Nat.min_eq_left (by simp only [headerLength] at h9; omega), hA]
    have c3 := atLeast_of_lt (headerLength + r.payload.length + 1) ((r.encode k o).take n)
      (by rw [htl]; omega)
    have c4 : ¬ (r.payload.length > maxPayload) := by omega
    simp only [c1, c2, c3, c4, h4, readLE_le _ _ hlen, spec_maxPayload, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, ↓reduceIte]

theorem getD_zeros (xs : Bytes) (k i : Nat) (h : xs.length ≤ i) :
    (xs ++ List.replicate k 0).getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, List.getElem?_replicate]
  split <;> rfl

/-- **A frame cut short and filled with zeros to its length** misses its end mark, wherever the
cut: the octet where its length, whatever of it is left, puts the mark is a zero. -/
theorem next_zeros (r : Record) (h : r.ok = true) (k : Bytes) (o : Nat) (key : Option Bytes)
    (offset n : Nat) (h0 : 0 < n) (hn : n < (r.encode k o).length) :
    next spec key offset ((r.encode k o).take n ++ List.replicate ((r.encode k o).length - n) 0) =
      .bad .unterminated := by
  have hp := payload_length r h
  have hlen : r.payload.length < 256 ^ 4 := by simp only [maxPayload] at hp; omega
  have hl := encode_length r k o
  have htl : ((r.encode k o).take n).length = n := by simp [List.length_take]; omega
  have hbl : ((r.encode k o).take n ++ List.replicate ((r.encode k o).length - n) 0).length =
      (r.encode k o).length := by
    simp only [List.length_append, htl, List.length_replicate]; omega
  have hA : (r.encode k o).take 4 = le 4 r.payload.length := by
    simp [Record.encode, frame, List.take_left', le_length]
  obtain ⟨len, hlen4, hle, hat⟩ : ∃ len,
      readLE (((r.encode k o).take n ++ List.replicate ((r.encode k o).length - n) 0).take 4) =
        len ∧ len ≤ r.payload.length ∧ n ≤ headerLength + len := by
    by_cases h4 : 4 ≤ n
    · refine ⟨r.payload.length, ?_, Nat.le_refl _, by simp only [headerLength] at hl ⊢; omega⟩
      rw [List.take_append_of_le_length (by rw [htl]; exact h4), List.take_take,
        Nat.min_eq_left h4, hA, readLE_le _ _ hlen]
    · refine ⟨_, rfl, ?_, by simp only [headerLength]; omega⟩
      have hA' : (r.encode k o).take n = (le 4 r.payload.length).take n := by
        rw [← hA, List.take_take, Nat.min_eq_left (by omega)]
      rw [List.take_append, htl, hA', List.take_replicate, readLE_zeros]
      have := readLE_take_le 4 n r.payload.length
      have e : ((le 4 r.payload.length).take n).take 4 = (le 4 r.payload.length).take n := by
        rw [List.take_take, Nat.min_eq_right (by omega)]
      rw [e]; exact this
  have hz : ((r.encode k o).take n ++ List.replicate ((r.encode k o).length - n) 0).getD
      (headerLength + len) 0 = 0 := getD_zeros _ _ _ (by rw [htl]; exact hat)
  generalize (r.encode k o).take n ++ List.replicate ((r.encode k o).length - n) 0 = bs
    at hbl hlen4 hz
  have c1 := isEmpty_of_length bs (by rw [hbl]; omega)
  have c2 := atLeast_of_le headerLength bs (by rw [hbl]; simp only [headerLength] at hl ⊢; omega)
  have c3 : ¬ (len > maxPayload) := by omega
  have c4 := atLeast_of_le (headerLength + len + 1) bs (by rw [hbl]; omega)
  have c5 : ((0 : Byte) != endMark) = true := by decide
  unfold next
  simp only [hlen4, hz, c1, c2, c3, c4, c5, spec_maxPayload, spec_ended, Bool.not_true,
    Bool.true_and, Bool.false_eq_true, ↓reduceIte]

/-- **A frame cut after its length and filled to its length** with octets that do not end in the
end mark misses it. -/
theorem next_fill (r : Record) (h : r.ok = true) (k : Bytes) (o : Nat) (key : Option Bytes)
    (offset n : Nat) (h4 : 4 ≤ n) (z : Bytes) (b : Byte)
    (hz : n + z.length + 1 = (r.encode k o).length) (hb : b ≠ endMark) :
    next spec key offset ((r.encode k o).take n ++ z ++ [b]) = .bad .unterminated := by
  have hp := payload_length r h
  have hlen : r.payload.length < 256 ^ 4 := by simp only [maxPayload] at hp; omega
  have hl := encode_length r k o
  have htl : ((r.encode k o).take n).length = n := by simp [List.length_take]; omega
  have hbl : ((r.encode k o).take n ++ z ++ [b]).length = (r.encode k o).length := by
    simp only [List.length_append, htl, List.length_singleton]; omega
  have hA : (r.encode k o).take 4 = le 4 r.payload.length := by
    simp [Record.encode, frame, List.take_left', le_length]
  have h4' : ((r.encode k o).take n ++ z ++ [b]).take 4 = le 4 r.payload.length := by
    rw [List.append_assoc, List.take_append_of_le_length (by rw [htl]; exact h4), List.take_take,
      Nat.min_eq_left h4, hA]
  have hgb : ((r.encode k o).take n ++ z ++ [b]).getD (headerLength + r.payload.length) 0 = b := by
    rw [show headerLength + r.payload.length = ((r.encode k o).take n ++ z).length by
      simp only [List.length_append, htl, headerLength] at hl ⊢; omega]
    simp [List.getD_eq_getElem?_getD]
  have hl4 : readLE (((r.encode k o).take n ++ z ++ [b]).take 4) = r.payload.length := by
    rw [h4', readLE_le _ _ hlen]
  generalize (r.encode k o).take n ++ z ++ [b] = bs at hbl hl4 hgb
  have c1 := isEmpty_of_length bs (by rw [hbl]; omega)
  have c2 := atLeast_of_le headerLength bs (by rw [hbl]; simp only [headerLength] at hl ⊢; omega)
  have c3 : ¬ (r.payload.length > maxPayload) := by omega
  have c4 := atLeast_of_le (headerLength + r.payload.length + 1) bs (by rw [hbl]; omega)
  have c5 : (b != endMark) = true := by simp [hb]
  unfold next
  simp only [hl4, hgb, c1, c2, c3, c4, c5, spec_maxPayload, spec_ended, Bool.not_true,
    Bool.true_and, Bool.false_eq_true, ↓reduceIte]

/-- **A torn append reads as a torn tail**: after the records, any proper prefix of a frame is
taken for a torn tail at the offset where it starts, when it is quiet. -/
theorem scan_torn (k : Bytes) (hk : k.length = keyLength) (cs : List Record) (hcs : Appends cs)
    (r : Record) (hr : r.ok = true) (k' : Bytes) (o n : Nat) (h0 : 0 < n)
    (hn : n < (r.encode k' o).length)
    (hq : Quiet k (journal k cs).length ((r.encode k' o).take n)) :
    scan (journal k cs ++ (r.encode k' o).take n) =
      ⟨.format k :: cs, .torn (journal k cs).length⟩ :=
  scan_stop k hk cs hcs _ .short (next_short r hr k' o _ _ n h0 hn) rfl
    (by have := encode_le r hr k' o; rw [List.length_take]; omega) hq

/-- **A torn append filled with zeros reads as a torn tail**, wherever the cut, when it is
quiet. -/
theorem scan_torn_zeros (k : Bytes) (hk : k.length = keyLength) (cs : List Record)
    (hcs : Appends cs) (r : Record) (hr : r.ok = true) (k' : Bytes) (o n : Nat) (h0 : 0 < n)
    (hn : n < (r.encode k' o).length)
    (hq : Quiet k (journal k cs).length
      ((r.encode k' o).take n ++ List.replicate ((r.encode k' o).length - n) 0)) :
    scan (journal k cs ++
        ((r.encode k' o).take n ++ List.replicate ((r.encode k' o).length - n) 0)) =
      ⟨.format k :: cs, .torn (journal k cs).length⟩ :=
  scan_stop k hk cs hcs _ .unterminated (next_zeros r hr k' o _ _ n h0 hn) rfl
    (by have := encode_le r hr k' o; simp only [List.length_append, List.length_take,
      List.length_replicate]; omega) hq

/-- **A torn append cut after its length and filled with anything not ending in the end mark
reads as a torn tail**, when it is quiet. -/
theorem scan_torn_fill (k : Bytes) (hk : k.length = keyLength) (cs : List Record)
    (hcs : Appends cs) (r : Record) (hr : r.ok = true) (k' : Bytes) (o n : Nat) (h4 : 4 ≤ n)
    (z : Bytes) (b : Byte) (hz : n + z.length + 1 = (r.encode k' o).length) (hb : b ≠ endMark)
    (hq : Quiet k (journal k cs).length ((r.encode k' o).take n ++ z ++ [b])) :
    scan (journal k cs ++ ((r.encode k' o).take n ++ z ++ [b])) =
      ⟨.format k :: cs, .torn (journal k cs).length⟩ :=
  scan_stop k hk cs hcs _ .unterminated (next_fill r hr k' o _ _ n h4 z b hz hb) rfl
    (by have := encode_le r hr k' o; simp only [List.length_append, List.length_take,
      List.length_singleton]; omega) hq

/-- A journal whose format record the crash cut short reads as a torn tail at its start. -/
theorem scan_torn_format (k : Bytes) (hk : k.length = keyLength) (n : Nat) (h0 : 0 < n)
    (hn : n < ((Record.format k).encode k 0).length) :
    scan (((Record.format k).encode k 0).take n) = ⟨[], .torn 0⟩ :=
  scan_stop_first _ .short (next_short (.format k) (by simp [Record.ok, hk]) k 0 _ _ n h0 hn) rfl
    (by rw [List.length_take, ← format_encode_length k hk 0]; omega)

/-- So does one whose format record the crash cut short and filled with zeros. -/
theorem scan_torn_format_zeros (k : Bytes) (hk : k.length = keyLength) (n : Nat) (h0 : 0 < n)
    (hn : n < ((Record.format k).encode k 0).length) :
    scan (((Record.format k).encode k 0).take n ++
        List.replicate (((Record.format k).encode k 0).length - n) 0) = ⟨[], .torn 0⟩ :=
  scan_stop_first _ .unterminated
    (next_zeros (.format k) (by simp [Record.ok, hk]) k 0 _ _ n h0 hn) rfl
    (by simp only [List.length_append, List.length_take, List.length_replicate]
        rw [← format_encode_length k hk 0]; omega)

/-- And so does one whose format record the crash cut after its length and filled with anything
not ending in the end mark. -/
theorem scan_torn_format_fill (k : Bytes) (hk : k.length = keyLength) (n : Nat) (h4 : 4 ≤ n)
    (z : Bytes) (b : Byte) (hz : n + z.length + 1 = ((Record.format k).encode k 0).length)
    (hb : b ≠ endMark) :
    scan (((Record.format k).encode k 0).take n ++ z ++ [b]) = ⟨[], .torn 0⟩ :=
  scan_stop_first _ .unterminated
    (next_fill (.format k) (by simp [Record.ok, hk]) k 0 _ _ n h4 z b hz hb) rfl
    (by simp only [List.length_append, List.length_take, List.length_singleton]
        rw [← format_encode_length k hk 0]; omega)

/-! ## What reading looks at -/

/-- **Reading a frame looks at no octet past it**: a frame read as a record is read the same from
any prefix that holds it, and what follows it is cut to that prefix. -/
theorem next_take (r : Rules) (key : Option Bytes) (offset : Nat) (bs : Bytes) (rec : Record)
    (taken : Nat) (rest : Bytes) (h : next r key offset bs = .record rec taken rest) (m : Nat)
    (hm : taken ≤ m) :
    0 < taken ∧ taken ≤ bs.length ∧ rest = bs.drop taken ∧
      next r key offset (bs.take m) = .record rec taken (rest.take (m - taken)) := by
  unfold next at h
  by_cases c1 : bs.isEmpty = true
  · rw [if_pos c1] at h; cases h
  rw [if_neg c1] at h
  by_cases c2 : (!atLeast headerLength bs) = true
  · rw [if_pos c2] at h; cases h
  rw [if_neg c2] at h
  dsimp only at h
  generalize hl : readLE (bs.take 4) = len at h
  by_cases c3 : len > r.maxPayload
  · rw [if_pos c3] at h; cases h
  rw [if_neg c3] at h
  by_cases c4 : (!atLeast (headerLength + len + 1) bs) = true
  · rw [if_pos c4] at h; cases h
  rw [if_neg c4] at h
  by_cases c5 : (r.ended && bs.getD (headerLength + len) 0 != endMark) = true
  · rw [if_pos c5] at h; cases h
  rw [if_neg c5] at h
  generalize hb : (bs.drop 12).take (1 + len) = body at h
  rcases body with _ | ⟨t, payload⟩
  · cases h
  generalize ht : readLE ((bs.drop 4).take 8) = stored at h
  by_cases c6 : (r.tagged && tagWrong (key <|> keyIn r t.toNat payload) stored offset t.toNat
      payload) = true
  · dsimp only at h; rw [if_pos c6] at h; cases h
  dsimp only at h
  rw [if_neg c6] at h
  generalize hr : recordOf r t.toNat payload = found at h
  rcases found with _ | rec'
  · cases h
  dsimp only at h
  simp only [Next.record.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  simp only [Bool.not_eq_true', atLeast_eq, decide_eq_false_iff_not, Decidable.not_not] at c4
  refine ⟨by omega, by omega, rfl, ?_⟩
  simp only [headerLength] at c4 hm ⊢
  have hm4 : 4 ≤ m := by omega
  unfold next
  have d1 : (bs.take m).isEmpty = false := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    cases bs with
    | nil => simp at c4
    | cons _ _ => rfl
  have d2 : atLeast 13 (bs.take m) = true := by
    rw [atLeast_eq]; simp only [List.length_take, decide_eq_true_eq]; omega
  have d3 : (bs.take m).take 4 = bs.take 4 := by rw [List.take_take, Nat.min_eq_left hm4]
  have d4 : atLeast (13 + len + 1) (bs.take m) = true := by
    rw [atLeast_eq]; simp only [List.length_take, decide_eq_true_eq]; omega
  have d5 : (bs.take m).getD (13 + len) 0 = bs.getD (13 + len) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
    rw [if_pos (by omega)]
  have d6 : ((bs.take m).drop 12).take (1 + len) = (bs.drop 12).take (1 + len) := by
    rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
  have d7 : ((bs.take m).drop 4).take 8 = (bs.drop 4).take 8 := by
    rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
  have d8 : (bs.take m).drop (13 + len + 1) = (bs.drop (13 + len + 1)).take (m - (13 + len + 1)) :=
    List.drop_take
  simp only [headerLength] at c2 c5 hb
  simp only [headerLength, d1, d2, d3, hl, c3, d4, d5, d6, d7, ht, hb, d8, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte] at c5 ⊢
  simp only [Bool.not_eq_true] at c5 c6
  simp only [c5, c6, Bool.false_eq_true, ↓reduceIte, hr]

/-- Reading stops in a torn tail no earlier than where it started. -/
theorem scanFrom_torn_ge (r : Rules) :
    ∀ (fuel : Nat) (bs : Bytes) (off : Nat) (key : Option Bytes) (acc rs : List Record) (x : Nat),
      scanFrom r fuel bs off key acc = ⟨rs, .torn x⟩ → off ≤ x
  | 0, _, _, _, _, _, _, h => by simp [scanFrom] at h
  | fuel + 1, bs, off, key, acc, rs, x, h => by
    cases hn : next r key off bs with
    | done => simp [scanFrom, hn] at h
    | bad w =>
      simp only [scanFrom, hn, Scan.mk.injEq] at h
      rcases stop_cases r off bs key w with e | e <;> rw [e] at h <;> simp at h
      omega
    | record rec taken rest =>
      simp only [scanFrom, hn] at h
      split at h
      · simp at h
      · have := scanFrom_torn_ge r fuel rest (off + taken) _ _ rs x h
        omega

/-- Reading up to a torn tail reads the same records and ends cleanly there. -/
theorem scanFrom_take (r : Rules) :
    ∀ (fuel : Nat) (bs : Bytes) (off : Nat) (key : Option Bytes) (acc rs : List Record) (x : Nat),
      scanFrom r fuel bs off key acc = ⟨rs, .torn x⟩ → ∀ fuel', (bs.take (x - off)).length < fuel' →
        scanFrom r fuel' (bs.take (x - off)) off key acc = ⟨rs, .clean⟩
  | 0, _, _, _, _, _, _, h, _, _ => by simp [scanFrom] at h
  | fuel + 1, bs, off, key, acc, rs, x, h, fuel', hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel' = f + 1 := ⟨fuel' - 1, by omega⟩
    cases hn : next r key off bs with
    | done => simp [scanFrom, hn] at h
    | bad w =>
      simp only [scanFrom, hn, Scan.mk.injEq] at h
      rcases stop_cases r off bs key w with e | e <;> rw [e] at h
      · obtain ⟨rfl, hx⟩ := h
        simp only [End.torn.injEq] at hx
        subst hx
        simp [scanFrom, next]
      · simp at h
    | record rec taken rest =>
      simp only [scanFrom, hn] at h
      split at h
      · simp at h
      · rename_i hfa
        have hat := scanFrom_torn_ge r fuel rest (off + taken) _ _ rs x h
        obtain ⟨hpos, hlt, hrest, htake⟩ := next_take r key off bs rec taken rest hn (x - off)
          (by omega)
        have ih := scanFrom_take r fuel rest (off + taken) _ _ rs x h f
        simp only [scanFrom, htake, hfa, Bool.false_eq_true, ↓reduceIte]
        have e : x - off - taken = x - (off + taken) := by omega
        rw [e]
        apply ih
        subst hrest
        simp only [List.length_take, List.length_drop] at hf ⊢
        omega

/-- Reading stops in a torn tail before the end of what it reads. -/
theorem scanFrom_torn_lt (r : Rules) :
    ∀ (fuel : Nat) (bs : Bytes) (off : Nat) (key : Option Bytes) (acc rs : List Record) (x : Nat),
      scanFrom r fuel bs off key acc = ⟨rs, .torn x⟩ → x < off + bs.length
  | 0, _, _, _, _, _, _, h => by simp [scanFrom] at h
  | fuel + 1, bs, off, key, acc, rs, x, h => by
    cases hn : next r key off bs with
    | done => simp [scanFrom, hn] at h
    | bad w =>
      simp only [scanFrom, hn, Scan.mk.injEq] at h
      have hpos : 0 < bs.length := by
        cases bs with
        | nil => simp [next] at hn
        | cons _ _ => simp
      rcases stop_cases r off bs key w with e | e <;> rw [e] at h <;> simp at h
      omega
    | record rec taken rest =>
      simp only [scanFrom, hn] at h
      split at h
      · simp at h
      · obtain ⟨_, hlt, hrest, _⟩ := next_take r key off bs rec taken rest hn taken (Nat.le_refl _)
        have := scanFrom_torn_lt r fuel rest (off + taken) _ _ rs x h
        subst hrest
        simp only [List.length_drop] at this
        omega

/-- A journal's torn tail starts within it. -/
theorem scan_torn_le (bs : Bytes) (rs : List Record) (x : Nat) (h : scan bs = ⟨rs, .torn x⟩) :
    x ≤ bs.length := by
  simp only [scan, scanWith] at h
  have := scanFrom_torn_lt spec _ bs 0 none [] rs x h
  omega

/-- **Reading a journal up to its torn tail reads cleanly**: the octets before the tail hold the
same records, and nothing after them. -/
theorem scan_take (bs : Bytes) (rs : List Record) (x : Nat) (h : scan bs = ⟨rs, .torn x⟩) :
    scan (bs.take x) = ⟨rs, .clean⟩ := by
  simp only [scan, scanWith] at h ⊢
  have := scanFrom_take spec _ bs 0 none [] rs x h ((bs.take x).length + 1)
    (by rw [Nat.sub_zero]; omega)
  simpa using this

/-! ## Every rule of reading matters -/

/-- A version of the rules of reading with one of them changed. -/
inductive Mutant
  | none
  /-- the tag not checked -/
  | tagUnchecked
  /-- a torn tail one octet longer -/
  | tornLonger
  /-- a torn tail one octet shorter -/
  | tornShorter
  /-- a payload one octet longer than any commit's taken -/
  | lengthLonger
  /-- the largest commit's payload refused -/
  | lengthShorter
  /-- the end mark not checked -/
  | endUnchecked
  /-- before any record, a torn tail as long as the largest frame -/
  | tornAtStart
  /-- the format more than once -/
  | formatAgain
  /-- octets after a commit let be -/
  | inexact
  /-- a commit a correct store does not write taken -/
  | unchecked
  /-- a frame that checks but holds no record taken for a torn tail -/
  | notARecordTorn
  /-- a torn tail taken whatever checks after its first octet -/
  | laterUnchecked
  /-- the last sixteen octets of any first frame taken for its key -/
  | unshaped
  deriving DecidableEq

def rulesOf : Mutant → Rules
  | .none => spec
  | .tagUnchecked => { tagged := false }
  | .tornLonger => { maxFrame := maxFrame + 1 }
  | .tornShorter => { maxFrame := maxFrame - 1 }
  | .lengthLonger => { maxPayload := maxPayload + 1 }
  | .lengthShorter => { maxPayload := maxPayload - 1 }
  | .endUnchecked => { ended := false }
  | .tornAtStart => { firstFrame := maxFrame }
  | .formatAgain => { formatOnce := false }
  | .inexact => { exact := false }
  | .unchecked => { checked := false }
  | .notARecordTorn => { strict := false }
  | .laterUnchecked => { quiet := false }
  | .unshaped => { shaped := false }

def names : List (String × Mutant) :=
  [("tag-unchecked", .tagUnchecked), ("torn-longer", .tornLonger),
   ("torn-shorter", .tornShorter), ("length-longer", .lengthLonger),
   ("length-shorter", .lengthShorter), ("end-unchecked", .endUnchecked),
   ("torn-at-start", .tornAtStart), ("format-again", .formatAgain), ("inexact", .inexact),
   ("unchecked", .unchecked), ("not-a-record-torn", .notARecordTorn),
   ("later-unchecked", .laterUnchecked), ("key-unshaped", .unshaped)]

/-- A key for the examples. -/
def sampleKey : Bytes := (List.range 16).map (BitVec.ofNat 8 ·)

/-- A commit for the examples. -/
def sample : Commit :=
  ⟨1, ascii "<a@b.example>", [⟨ascii "local.test", 1⟩], 100, 200, 12345⟩

/-- The premise `Appends` can hold: of the sample's commit and a start. -/
theorem appends_witness : Appends [.commit sample, .start] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨by decide, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- The premise `Quiet` can hold: of an octet alone, after which nothing starts. -/
theorem quiet_witness : Quiet sampleKey 0 [0] := rfl

/-- A journal of the sample key's format alone, and a frame appended after it. -/
def after (type : Nat) (payload : Bytes) : Bytes :=
  let j := journal sampleKey []
  j ++ frame sampleKey j.length type payload

/-- A journal that tells the rules with one changed from the rules. None makes the kernel compute
a tag over more than a small frame. -/
def witness : Mutant → Bytes
  | .none => journal sampleKey []
  | .tagUnchecked =>
    let j := journal sampleKey [.commit sample]
    j.set (j.length - 20) (BitVec.ofNat 8 120)
  | .tornLonger => journal sampleKey [] ++ List.replicate (maxFrame + 1) 0
  | .tornShorter => journal sampleKey [] ++ List.replicate maxFrame 0
  | .lengthLonger =>
    journal sampleKey [] ++ le 4 (maxPayload + 1) ++ List.replicate (maxFrame + 1) 0
  | .lengthShorter => journal sampleKey [] ++ le 4 maxPayload ++ List.replicate (maxFrame + 1) 0
  | .endUnchecked => (after commitType sample.payload).dropLast ++ [0]
  | .tornAtStart => List.replicate (firstFrame + 1) 0
  | .formatAgain => after formatType (magic ++ sampleKey)
  | .inexact => after commitType (sample.payload ++ [0])
  | .unchecked => after commitType { sample with messageId := [] }.payload
  | .notARecordTorn => after 4 sample.payload
  | .laterUnchecked => journal sampleKey [] ++ 0 :: Record.start.encode sampleKey (firstFrame + 1)
  | .unshaped => frame sampleKey 0 commitType (magic ++ sampleKey)

/-- **Each rule of reading matters**: with it changed, its witness reads otherwise. -/
theorem mutants_differ : ∀ m, m ≠ .none →
    scanWith (rulesOf m) (witness m) ≠ scan (witness m) := by
  intro m hm
  cases m <;> first | exact absurd rfl hm | decide +kernel

/-! ## What is proven of names -/

theorem digitValue_hexDigit : ∀ d, d < 16 → digitValue (hexDigit d) = some d := by decide

theorem hexOf_length (k n : Nat) : (hexOf k n).length = k := by
  induction k <;> simp_all [hexOf]

theorem foldl_hexOf (k n acc : Nat) :
    (hexOf k n).foldlM hexStep acc = some (acc * 16 ^ k + n % 16 ^ k) := by
  induction k generalizing acc with
  | zero => simp [hexOf, Nat.mod_one]
  | succ k ih =>
    have hd : hexStep acc (hexDigit (n / 16 ^ k % 16)) = some (16 * acc + n / 16 ^ k % 16) := by
      simp [hexStep, digitValue_hexDigit _ (Nat.mod_lt _ (by decide))]
    simp only [hexOf, List.foldlM_cons, hd, Option.bind_eq_bind, Option.bind_some, ih]
    rw [Nat.pow_succ, Nat.mod_mul]
    congr 1
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
    omega

theorem hexValue_hex16 (n : Nat) (h : n < 2 ^ 64) : hexValue (hex16 n) = some n := by
  have h16 : n % 16 ^ 16 = n := Nat.mod_eq_of_lt (by simpa using h)
  simp only [hexValue, hex16, hexOf_length, ↓reduceIte, foldl_hexOf, h16]
  simp

/-- **The names the store gives read back as what they name.** -/
theorem parseName_bytes (n : Name) (h : n.valid = true) : parseName n.bytes = some n := by
  cases n with
  | journal => decide
  | final s | temp s | quarantine s | tail s =>
    simp only [Name.valid, decide_eq_true_eq] at h
    have hl : (hex16 s).length = 16 := hexOf_length _ _
    simp only [Name.bytes, parseName, finalName, tempName, quarantineName, tailName, journalName]
    rw [if_neg (by intro e; rw [beq_iff_eq] at e; have := congrArg List.length e
                   simp [ascii, hl] at this)]
    simp [ascii, hexValue_hex16 s h]

theorem digitValue_lt (b : Byte) (d : Nat) (h : digitValue b = some d) : d < 16 := by
  unfold digitValue at h
  split at h
  · simp only [Option.some.injEq] at h; omega
  · split at h
    · simp only [Option.some.injEq] at h; omega
    · simp at h

theorem foldlM_hexStep_lt : ∀ (ds : Bytes) (acc v : Nat), ds.foldlM hexStep acc = some v →
    v < (acc + 1) * 16 ^ ds.length
  | [], acc, v, h => by simp only [List.foldlM_nil, pure, Option.some.injEq] at h; subst h; simp
  | d :: ds, acc, v, h => by
    simp only [List.foldlM_cons] at h
    cases hd : hexStep acc d with
    | none => simp [hd] at h
    | some a =>
      simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
      have ih := foldlM_hexStep_lt ds a v h
      simp only [hexStep, Option.map_eq_some_iff] at hd
      obtain ⟨dv, hdv, rfl⟩ := hd
      have := digitValue_lt d dv hdv
      have hle : (16 * acc + dv + 1) * 16 ^ ds.length ≤ (acc + 1) * 16 ^ (d :: ds).length := by
        rw [List.length_cons, Nat.pow_succ, Nat.mul_comm (16 ^ ds.length) 16, ← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (by omega)
      omega

/-- **Every name the store reads carries a number below 2 ^ 64.** -/
theorem parseName_valid (b : Bytes) (n : Name) (h : parseName b = some n) : n.valid = true := by
  have hv : ∀ ds v, hexValue ds = some v → v < 2 ^ 64 := by
    intro ds v hd
    simp only [hexValue] at hd
    split at hd
    · rename_i hl
      have := foldlM_hexStep_lt ds 0 v hd
      rw [hl] at this
      simpa using this
    · simp at hd
  unfold parseName at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · split at h
    · repeat' (split at h)
      all_goals
        try simp only [Option.map_eq_some_iff, Functor.map] at h
      all_goals first
        | (obtain ⟨v, hv', rfl⟩ := h
           simp [Name.valid, hv _ v hv'])
        | simp at h
    · simp at h

/-- **Different files get different names**: of any kind, their numbers below 2 ^ 64. -/
theorem names_injective (n m : Name) (hn : n.valid = true) (hm : m.valid = true)
    (e : n.bytes = m.bytes) : n = m := by
  have h := parseName_bytes n hn
  rw [e, parseName_bytes m hm] at h
  exact (Option.some.inj h).symm

end DN.News.Journal
