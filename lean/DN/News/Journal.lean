-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.CommandSpec

/-!
# DN.News.Journal

The store's journal and the names of its files, as docs/decisions/0005-article-store.md ("On
disk") fixes them: the CRC-32C that checks every record, how a record is framed and what it
holds, the names of the store's files, and how a journal is read back — its records in order,
and how it ends: cleanly, in a torn tail the next start truncates, or in corruption that keeps
the store from starting.

A record is framed as `length ‖ crc ‖ type ‖ payload ‖ end`: the payload's length and the CRC-32C
of the type and the payload, each four octets, least significant first, then the type, one octet,
the payload, and the end mark, one octet. The journal's first record names its format; each other
one is the commit of an article: its number in the store, its message identifier, each group it
goes to with the number it has there, the size of its header section and of its file, and the
file's CRC-32C.

Reading stops at the first frame that does not check. If it is short, its length past any
payload's, its end mark missing or its CRC-32C wrong — what an append the crash cut short can
leave — and what is left is no longer than the one append that can have been cut, it is a torn
tail, which the next start truncates: the format's frame while no record has been read, the
largest frame after. Anything longer is corruption, and so is, wherever it is, a frame that
checks but holds no record, a format of another version among them; a journal whose first record
is not its format; and a format again.

Proven: a journal of records reads back as those records (`scan_encoded`); after them, a frame
cut short reads as a torn tail where it starts, whether the crash left a proper prefix of it
(`scan_torn`), that prefix and zeros to the frame's length (`scan_torn_zeros`), or its length and
any octets to the frame's length but the end mark last (`scan_torn_fill`); so does the format's
frame cut short while it is alone (`scan_torn_format`, `scan_torn_format_zeros`,
`scan_torn_format_fill`). That the octets any other crash leaves never make a frame that checks —
the end mark where its length puts it and the CRC-32C right — is assumed.
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

inductive Record
  | format
  | commit (c : Commit)
  deriving DecidableEq

def formatType : Nat := 1
def commitType : Nat := 2

/-- What the format record holds: the journal's name for itself and its version, one octet. -/
def formatPayload : Bytes := ascii "dragons-net journal" ++ [BitVec.ofNat 8 1]

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

/-- The octets before a payload: its length, the CRC and the type. -/
def headerLength : Nat := 9

/-- The most octets a payload holds: that of the largest commit. -/
def maxPayload : Nat := 8 + (1 + 250) + (1 + 16 * (1 + 64 + 4)) + 4 + 4 + 4

/-- The largest frame, the most one append writes. -/
def maxFrame : Nat := headerLength + maxPayload + 1

/-- The format's frame, the only append a journal without records can have had cut short. -/
def firstFrame : Nat := headerLength + formatPayload.length + 1

def frame (type : Nat) (payload : Bytes) : Bytes :=
  le 4 payload.length ++ le 4 (crc32c (BitVec.ofNat 8 type :: payload)).toNat ++
    (BitVec.ofNat 8 type :: payload) ++ [endMark]

def Record.encode : Record → Bytes
  | .format => frame formatType formatPayload
  | .commit c => frame commitType c.payload

/-- The records encoded one after the other. -/
def encodeAll (rs : List Record) : Bytes := (rs.map Record.encode).flatten

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
  /-- its CRC-32C is not that of its type and payload -/
  | checksum
  /-- it checks, but is no record the journal holds -/
  | notARecord
  /-- the journal's first record is not its format -/
  | noFormat
  /-- a second format record -/
  | formatAgain
  deriving DecidableEq

/-- Whether an append the crash cut short can leave a frame that fails so. -/
def Why.torn : Why → Bool
  | .short | .tooLong | .unterminated | .checksum => true
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
  /-- whether the CRC-32C is checked -/
  crc : Bool := true
  /-- whether the journal has to begin with its format -/
  formatFirst : Bool := true
  /-- whether the format may appear only once -/
  formatOnce : Bool := true
  /-- whether a commit has to take its whole payload -/
  exact : Bool := true
  /-- whether a commit has to be one a correct store writes -/
  checked : Bool := true
  /-- whether only a frame a torn append can leave may be a torn tail -/
  strict : Bool := true

def spec : Rules := {}

/-- The record a type and payload make, if they make one. -/
def recordOf (r : Rules) (type : Nat) (payload : Bytes) : Option Record :=
  if type == formatType && payload == formatPayload then some .format
  else if type == commitType then
    (decodeCommit payload r.exact r.checked).map .commit
  else none

/-- The frame at the start of `bs`. The end mark is checked before the CRC-32C, so that a frame
cut short and filled is known without it. -/
def next (r : Rules) (bs : Bytes) : Next :=
  if bs.isEmpty then .done
  else if bs.length < headerLength then .bad .short
  else
    let len := readLE (bs.take 4)
    if len > r.maxPayload then .bad .tooLong
    else if bs.length < headerLength + len + 1 then .bad .short
    else if r.ended && bs.getD (headerLength + len) 0 != endMark then .bad .unterminated
    else
      let body := (bs.drop 8).take (1 + len)
      if r.crc && readLE ((bs.drop 4).take 4) != (crc32c body).toNat then .bad .checksum
      else
        match body with
        | t :: payload =>
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

/-- What stops reading at `offset`, with `left` octets after it, `first` if no record has been
read: a torn tail if a torn append can leave the frame and they fit the append that can have been
cut, corruption otherwise. -/
def stop (r : Rules) (offset left : Nat) (first : Bool) (why : Why) : End :=
  if (why.torn || !r.strict) && left ≤ (if first then r.firstFrame else r.maxFrame) then
    .torn offset
  else .corrupt offset why

/-- Reading from `offset`, `fuel` records at most; each record takes more than `headerLength`
octets, so `scanWith` gives fuel enough and the first case is never met. -/
def scanFrom (r : Rules) : Nat → Bytes → Nat → List Record → Scan
  | 0, _, offset, acc => ⟨acc.reverse, .corrupt offset .tooLong⟩
  | fuel + 1, bs, offset, acc =>
    match next r bs with
    | .done => ⟨acc.reverse, .clean⟩
    | .bad why => ⟨acc.reverse, stop r offset bs.length acc.isEmpty why⟩
    | .record rec taken rest =>
      if r.formatFirst && acc.isEmpty && rec != .format then
        ⟨[], .corrupt offset .noFormat⟩
      else if r.formatOnce && !acc.isEmpty && rec == .format then
        ⟨acc.reverse, .corrupt offset .formatAgain⟩
      else scanFrom r fuel rest (offset + taken) (rec :: acc)

/-- **How a journal reads back**, under rules `r`. Each record takes more than `headerLength`
octets, so the length of the journal is fuel enough. -/
def scanWith (r : Rules) (bs : Bytes) : Scan := scanFrom r (bs.length + 1) bs 0 []

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

/-- A name the store gives a file. -/
inductive Name
  | journal
  | final (seq : Nat)
  | temp (seq : Nat)
  deriving DecidableEq

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
  | .format => true
  | .commit c => c.ok

def Record.payload : Record → Bytes
  | .format => formatPayload
  | .commit c => c.payload

def Record.type : Record → Nat
  | .format => formatType
  | .commit _ => commitType

theorem encode_frame (r : Record) : r.encode = frame r.type r.payload := by
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
  | format => decide
  | commit c =>
    simp only [Record.ok, Commit.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hm2⟩, _⟩, hg2⟩, hgs⟩, _⟩, _⟩, _⟩, _⟩ := h
    have := groups_length c.groups (fun g hg => by have := hgs g hg; omega)
    simp only [Record.payload, Commit.payload, List.length_append, List.length_cons, le_length,
      maxPayload]
    omega

theorem encode_length (r : Record) : r.encode.length = headerLength + r.payload.length + 1 := by
  rw [encode_frame]
  simp [frame, le_length, headerLength]
  omega

theorem encode_le (r : Record) (h : r.ok = true) : r.encode.length ≤ maxFrame := by
  have := payload_length r h
  rw [encode_length]
  simp only [maxFrame]
  omega

theorem format_encode_length : Record.format.encode.length = firstFrame := by
  rw [encode_length]; rfl

/-- A frame laid out as reading takes it apart. -/
theorem encode_shape (r : Record) (rest : Bytes) : r.encode ++ rest =
    (le 4 r.payload.length ++ le 4 (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest)) := by
  rw [encode_frame]; simp [frame]

theorem recordOf_payload (r : Record) (h : r.ok = true) :
    recordOf spec (BitVec.ofNat 8 r.type).toNat r.payload = some r := by
  cases r with
  | format => decide
  | commit c =>
    have hd := decode_payload c h
    simp [recordOf, Record.type, Record.payload, formatType, commitType, spec, hd]

/-- **A record reads back as itself**, whatever follows it. -/
theorem next_encode (r : Record) (h : r.ok = true) (rest : Bytes) :
    next spec (r.encode ++ rest) = .record r r.encode.length rest := by
  have hp := payload_length r h
  have hlen : r.payload.length < 256 ^ 4 := by simp only [maxPayload] at hp; omega
  have hcrc : (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat < 256 ^ 4 :=
    UInt32.toNat_lt _
  have hab : (le 4 r.payload.length ++
      le 4 (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat).length = 8 := by
    simp [le_length]
  have h4 : ((le 4 r.payload.length ++ le 4 (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).take 4 =
      le 4 r.payload.length := by
    rw [List.append_assoc]; exact List.take_left' (le_length _ _)
  have h44 : (((le 4 r.payload.length ++
      le 4 (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).drop 4).take 4 =
      le 4 (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat := by
    rw [List.append_assoc, List.drop_left' (le_length _ _)]; exact List.take_left' (le_length _ _)
  have hbody : (((le 4 r.payload.length ++
      le 4 (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).drop 8).take
        (1 + r.payload.length) = BitVec.ofNat 8 r.type :: r.payload := by
    rw [List.drop_left' hab, Nat.add_comm, List.take_succ_cons, List.take_left' rfl]
  have hend : ((le 4 r.payload.length ++
      le 4 (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).getD
        (headerLength + r.payload.length) 0 = endMark := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hab]; simp only [headerLength]; omega), hab,
      show headerLength + r.payload.length - 8 = r.payload.length + 1 by
        simp only [headerLength]; omega]
    simp
  have hrest : ((le 4 r.payload.length ++
      le 4 (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).drop
        (headerLength + r.payload.length + 1) = rest := by
    rw [show headerLength + r.payload.length + 1 = 8 + (r.payload.length + 2) by
      simp only [headerLength]; omega, ← List.drop_drop, List.drop_left' hab]
    simp
  have hfull : ((le 4 r.payload.length ++
      le 4 (crc32c (BitVec.ofNat 8 r.type :: r.payload)).toNat) ++
      (BitVec.ofNat 8 r.type :: (r.payload ++ endMark :: rest))).length =
      headerLength + r.payload.length + 1 + rest.length := by
    simp [le_length, headerLength]; omega
  have hl : ¬ (r.payload.length > maxPayload) := by omega
  have hr := recordOf_payload r h
  rw [encode_shape]
  unfold next
  simp only [spec] at hr ⊢
  rw [h4, readLE_le _ _ hlen, hend, h44, readLE_le _ _ hcrc, hbody, hrest]
  rw [if_neg (by rw [List.isEmpty_iff, ← List.length_eq_zero_iff, hfull]; omega),
    if_neg (by rw [hfull]; simp only [headerLength]; omega), if_neg hl,
    if_neg (by rw [hfull]; omega), if_neg (by simp), if_neg (by simp)]
  simp only [hr, encode_length]

@[simp] theorem spec_formatFirst : spec.formatFirst = true := rfl
@[simp] theorem spec_formatOnce : spec.formatOnce = true := rfl

theorem encodeAll_cons (r : Record) (rs : List Record) :
    encodeAll (r :: rs) = r.encode ++ encodeAll rs := rfl

theorem encodeAll_length (rs : List Record) : headerLength * rs.length ≤ (encodeAll rs).length := by
  induction rs with
  | nil => simp [encodeAll]
  | cons r rs ih =>
    rw [encodeAll_cons, List.length_append, encode_length, List.length_cons]
    simp only [Nat.mul_succ]
    omega

/-- Reading on through commits, once the format has been read. -/
theorem scanFrom_commits (cs : List Record) (hcs : ∀ r ∈ cs, r.ok = true ∧ r ≠ .format) :
    ∀ (fuel : Nat) (tail : Bytes) (off : Nat) (acc : List Record), cs.length < fuel → acc ≠ [] →
      scanFrom spec fuel (encodeAll cs ++ tail) off acc =
        scanFrom spec (fuel - cs.length) tail (off + (encodeAll cs).length)
          (cs.reverse ++ acc) := by
  induction cs with
  | nil => intro fuel tail off acc _ _; simp [encodeAll]
  | cons c cs ih =>
    intro fuel tail off acc hf hacc
    have hc := hcs c (by simp)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    rw [encodeAll_cons, List.append_assoc]
    simp only [scanFrom, next_encode c hc.1]
    have hne : acc.isEmpty = false := by cases acc <;> simp_all
    have hnf : (c == Record.format) = false := by simp [hc.2]
    simp only [spec_formatFirst, spec_formatOnce, hne, hnf, Bool.and_false, Bool.false_and,
      Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte]
    rw [ih (fun r hr => hcs r (by simp [hr])) f tail (off + c.encode.length) (c :: acc)
      (by simp at hf; omega) (by simp)]
    have e1 : f + 1 - (c :: cs).length = f - cs.length := by simp
    have e2 : off + (c.encode ++ encodeAll cs).length =
        off + c.encode.length + (encodeAll cs).length := by simp; omega
    have e3 : (c :: cs).reverse ++ acc = cs.reverse ++ c :: acc := by simp
    rw [e1, e2, e3]

/-- Reading on after a frame that reads as the format, then commits: what follows them is read
with the format and the commits taken. -/
theorem scan_after_format (F : Bytes) (h0 : 0 < F.length)
    (hF : ∀ rest, next spec (F ++ rest) = .record .format F.length rest)
    (cs : List Record) (hcs : ∀ r ∈ cs, r.ok = true ∧ r ≠ .format) (tail : Bytes) :
    ∃ g, scan (F ++ (encodeAll cs ++ tail)) =
      scanFrom spec (g + 1) tail (F.length + (encodeAll cs).length) (cs.reverse ++ [.format]) := by
  have hlen := encodeAll_length cs
  simp only [headerLength] at hlen
  obtain ⟨f, hfe⟩ : ∃ f, (F ++ (encodeAll cs ++ tail)).length + 1 = f + 1 := ⟨_, rfl⟩
  have hl : (F ++ (encodeAll cs ++ tail)).length =
      F.length + (encodeAll cs).length + tail.length := by
    simp only [List.length_append]; omega
  obtain ⟨g, hg⟩ : ∃ g, f - cs.length = g + 1 := ⟨f - cs.length - 1, by omega⟩
  refine ⟨g, ?_⟩
  rw [← hg]
  calc scan (F ++ (encodeAll cs ++ tail))
      = scanFrom spec (f + 1) (F ++ (encodeAll cs ++ tail)) 0 [] := by
        simp only [scan, scanWith]; rw [hfe]
    _ = scanFrom spec f (encodeAll cs ++ tail) (0 + F.length) [.format] := by
        simp only [scanFrom, hF, spec_formatFirst, spec_formatOnce, List.isEmpty_nil,
          bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
          Bool.false_and, Bool.true_and]
    _ = scanFrom spec (f - cs.length) tail (0 + F.length + (encodeAll cs).length)
          (cs.reverse ++ [.format]) :=
        scanFrom_commits cs hcs f tail (0 + F.length) [.format] (by omega) (by simp)
    _ = _ := by rw [Nat.zero_add]

/-- **A journal of records reads back as those records**, ending cleanly: its format, then its
commits. -/
theorem scan_encoded (cs : List Record) (hcs : ∀ r ∈ cs, r.ok = true ∧ r ≠ .format) :
    scan (encodeAll (.format :: cs)) = ⟨.format :: cs, .clean⟩ := by
  obtain ⟨g, hg⟩ := scan_after_format Record.format.encode
    (by rw [format_encode_length]; decide) (next_encode .format rfl) cs hcs []
  rw [List.append_nil] at hg
  rw [encodeAll_cons, hg]
  simp [scanFrom, next]

/-- After the records, what does not check for a reason a torn append can leave, and is no longer
than the largest frame, reads as a torn tail where it starts. -/
theorem scan_stop (cs : List Record) (hcs : ∀ r ∈ cs, r.ok = true ∧ r ≠ .format) (t : Bytes)
    (w : Why) (hw : next spec t = .bad w) (hwt : w.torn = true) (ht : t.length ≤ maxFrame) :
    scan (encodeAll (.format :: cs) ++ t) =
      ⟨.format :: cs, .torn (encodeAll (.format :: cs)).length⟩ := by
  obtain ⟨g, hg⟩ := scan_after_format Record.format.encode
    (by rw [format_encode_length]; decide) (next_encode .format rfl) cs hcs t
  rw [encodeAll_cons, List.append_assoc, hg]
  simp only [scanFrom, hw]
  simp [stop, hwt, ht, spec, List.length_append]

/-- Before any record, what does not check for a reason a torn append can leave, and is no longer
than the format's frame, reads as a torn tail at the start. -/
theorem scan_stop_first (t : Bytes) (w : Why) (hw : next spec t = .bad w) (hwt : w.torn = true)
    (ht : t.length ≤ firstFrame) : scan t = ⟨[], .torn 0⟩ := by
  simp only [scan, scanWith]
  obtain ⟨f, hfe⟩ : ∃ f, t.length + 1 = f + 1 := ⟨_, rfl⟩
  rw [hfe]
  simp only [scanFrom, hw]
  simp [stop, hwt, ht, spec]

/-- A proper prefix of a frame is short: its length says more than there is. -/
theorem next_short (r : Record) (h : r.ok = true) (n : Nat) (h0 : 0 < n)
    (hn : n < r.encode.length) : next spec (r.encode.take n) = .bad .short := by
  have hp := payload_length r h
  have hlen : r.payload.length < 256 ^ 4 := by simp only [maxPayload] at hp; omega
  have hl := encode_length r
  have htl : (r.encode.take n).length = n := by simp [List.length_take]; omega
  unfold next
  rw [if_neg (by rw [List.isEmpty_iff, ← List.length_eq_zero_iff, htl]; omega)]
  by_cases h9 : n < headerLength
  · rw [if_pos (by rw [htl]; exact h9)]
  · rw [if_neg (by rw [htl]; exact h9)]
    have h4 : (r.encode.take n).take 4 = le 4 r.payload.length := by
      rw [List.take_take, Nat.min_eq_left (by simp only [headerLength] at h9; omega), encode_frame]
      simp [frame, List.take_left', le_length]
    rw [h4, readLE_le _ _ hlen, if_neg (by simp only [spec]; omega),
      if_pos (by rw [htl]; simp only [headerLength] at hl ⊢; omega)]

theorem getD_zeros (xs : Bytes) (k i : Nat) (h : xs.length ≤ i) :
    (xs ++ List.replicate k 0).getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, List.getElem?_replicate]
  split <;> rfl

/-- **A frame cut short and filled with zeros to its length** misses its end mark, wherever the
cut: the octet where its length, whatever of it is left, puts the mark is a zero. -/
theorem next_zeros (r : Record) (h : r.ok = true) (n : Nat) (h0 : 0 < n)
    (hn : n < r.encode.length) :
    next spec (r.encode.take n ++ List.replicate (r.encode.length - n) 0) = .bad .unterminated := by
  have hp := payload_length r h
  have hlen : r.payload.length < 256 ^ 4 := by simp only [maxPayload] at hp; omega
  have hl := encode_length r
  have htl : (r.encode.take n).length = n := by simp [List.length_take]; omega
  have hbl : (r.encode.take n ++ List.replicate (r.encode.length - n) 0).length =
      r.encode.length := by
    simp only [List.length_append, htl, List.length_replicate]; omega
  have hA : r.encode.take 4 = le 4 r.payload.length := by
    rw [encode_frame]; simp [frame, List.take_left', le_length]
  obtain ⟨len, hlen4, hle, hat⟩ : ∃ len,
      readLE ((r.encode.take n ++ List.replicate (r.encode.length - n) 0).take 4) = len ∧
        len ≤ r.payload.length ∧ n ≤ headerLength + len := by
    by_cases h4 : 4 ≤ n
    · refine ⟨r.payload.length, ?_, Nat.le_refl _, by simp only [headerLength] at hl ⊢; omega⟩
      rw [List.take_append_of_le_length (by rw [htl]; exact h4), List.take_take,
        Nat.min_eq_left h4, hA, readLE_le _ _ hlen]
    · refine ⟨_, rfl, ?_, by simp only [headerLength]; omega⟩
      have hA' : r.encode.take n = (le 4 r.payload.length).take n := by
        rw [← hA, List.take_take, Nat.min_eq_left (by omega)]
      rw [List.take_append, htl, hA', List.take_replicate, readLE_zeros]
      have := readLE_take_le 4 n r.payload.length
      have e : ((le 4 r.payload.length).take n).take 4 = (le 4 r.payload.length).take n := by
        rw [List.take_take, Nat.min_eq_right (by omega)]
      rw [e]; exact this
  have hz : (r.encode.take n ++ List.replicate (r.encode.length - n) 0).getD
      (headerLength + len) 0 = 0 := getD_zeros _ _ _ (by rw [htl]; exact hat)
  generalize r.encode.take n ++ List.replicate (r.encode.length - n) 0 = bs at hbl hlen4 hz
  have c1 : ¬ (bs.isEmpty = true) := by
    rw [List.isEmpty_iff, ← List.length_eq_zero_iff, hbl]; omega
  have c2 : ¬ (bs.length < headerLength) := by rw [hbl]; simp only [headerLength] at hl ⊢; omega
  have c3 : ¬ (len > maxPayload) := by omega
  have c4 : ¬ (bs.length < headerLength + len + 1) := by rw [hbl]; omega
  have c5 : ((0 : Byte) != endMark) = true := by decide
  unfold next
  simp only [spec, hlen4, hz, c1, c2, c3, c4, c5, Bool.true_and, Bool.false_eq_true, ↓reduceIte]

/-- **A frame cut after its length and filled to its length** with octets that do not end in the
end mark misses it. -/
theorem next_fill (r : Record) (h : r.ok = true) (n : Nat) (h4 : 4 ≤ n) (z : Bytes) (b : Byte)
    (hz : n + z.length + 1 = r.encode.length) (hb : b ≠ endMark) :
    next spec (r.encode.take n ++ z ++ [b]) = .bad .unterminated := by
  have hp := payload_length r h
  have hlen : r.payload.length < 256 ^ 4 := by simp only [maxPayload] at hp; omega
  have hl := encode_length r
  have htl : (r.encode.take n).length = n := by simp [List.length_take]; omega
  have hbl : (r.encode.take n ++ z ++ [b]).length = r.encode.length := by
    simp only [List.length_append, htl, List.length_singleton]; omega
  have hA : r.encode.take 4 = le 4 r.payload.length := by
    rw [encode_frame]; simp [frame, List.take_left', le_length]
  have h4' : (r.encode.take n ++ z ++ [b]).take 4 = le 4 r.payload.length := by
    rw [List.append_assoc, List.take_append_of_le_length (by rw [htl]; exact h4), List.take_take,
      Nat.min_eq_left h4, hA]
  have hgb : (r.encode.take n ++ z ++ [b]).getD (headerLength + r.payload.length) 0 = b := by
    rw [show headerLength + r.payload.length = (r.encode.take n ++ z).length by
      simp only [List.length_append, htl, headerLength] at hl ⊢; omega]
    simp [List.getD_eq_getElem?_getD]
  have hl4 : readLE ((r.encode.take n ++ z ++ [b]).take 4) = r.payload.length := by
    rw [h4', readLE_le _ _ hlen]
  generalize r.encode.take n ++ z ++ [b] = bs at hbl hl4 hgb
  have c1 : ¬ (bs.isEmpty = true) := by
    rw [List.isEmpty_iff, ← List.length_eq_zero_iff, hbl]; omega
  have c2 : ¬ (bs.length < headerLength) := by rw [hbl]; simp only [headerLength] at hl ⊢; omega
  have c3 : ¬ (r.payload.length > maxPayload) := by omega
  have c4 : ¬ (bs.length < headerLength + r.payload.length + 1) := by rw [hbl]; omega
  have c5 : (b != endMark) = true := by simp [hb]
  unfold next
  simp only [spec, hl4, hgb, c1, c2, c3, c4, c5, Bool.true_and, Bool.false_eq_true, ↓reduceIte]

/-- **A torn append reads as a torn tail**: after the records, any proper prefix of a frame is
taken for a torn tail at the offset where it starts. -/
theorem scan_torn (cs : List Record) (hcs : ∀ r ∈ cs, r.ok = true ∧ r ≠ .format)
    (r : Record) (hr : r.ok = true) (n : Nat) (h0 : 0 < n) (hn : n < r.encode.length) :
    scan (encodeAll (.format :: cs) ++ r.encode.take n) =
      ⟨.format :: cs, .torn (encodeAll (.format :: cs)).length⟩ :=
  scan_stop cs hcs _ .short (next_short r hr n h0 hn) rfl
    (by have := encode_le r hr; rw [List.length_take]; omega)

/-- **A torn append filled with zeros reads as a torn tail**, wherever the cut. -/
theorem scan_torn_zeros (cs : List Record) (hcs : ∀ r ∈ cs, r.ok = true ∧ r ≠ .format)
    (r : Record) (hr : r.ok = true) (n : Nat) (h0 : 0 < n) (hn : n < r.encode.length) :
    scan (encodeAll (.format :: cs) ++
        (r.encode.take n ++ List.replicate (r.encode.length - n) 0)) =
      ⟨.format :: cs, .torn (encodeAll (.format :: cs)).length⟩ :=
  scan_stop cs hcs _ .unterminated (next_zeros r hr n h0 hn) rfl
    (by have := encode_le r hr; simp only [List.length_append, List.length_take,
      List.length_replicate]; omega)

/-- **A torn append cut after its length and filled with anything not ending in the end mark
reads as a torn tail.** -/
theorem scan_torn_fill (cs : List Record) (hcs : ∀ r ∈ cs, r.ok = true ∧ r ≠ .format)
    (r : Record) (hr : r.ok = true) (n : Nat) (h4 : 4 ≤ n) (z : Bytes) (b : Byte)
    (hz : n + z.length + 1 = r.encode.length) (hb : b ≠ endMark) :
    scan (encodeAll (.format :: cs) ++ (r.encode.take n ++ z ++ [b])) =
      ⟨.format :: cs, .torn (encodeAll (.format :: cs)).length⟩ :=
  scan_stop cs hcs _ .unterminated (next_fill r hr n h4 z b hz hb) rfl
    (by have := encode_le r hr; simp only [List.length_append, List.length_take,
      List.length_singleton]; omega)

/-- A journal whose format record the crash cut short reads as a torn tail at its start. -/
theorem scan_torn_format (n : Nat) (h0 : 0 < n) (hn : n < Record.format.encode.length) :
    scan (Record.format.encode.take n) = ⟨[], .torn 0⟩ :=
  scan_stop_first _ .short (next_short .format rfl n h0 hn) rfl
    (by rw [List.length_take, ← format_encode_length]; omega)

/-- So does one whose format record the crash cut short and filled with zeros. -/
theorem scan_torn_format_zeros (n : Nat) (h0 : 0 < n) (hn : n < Record.format.encode.length) :
    scan (Record.format.encode.take n ++ List.replicate (Record.format.encode.length - n) 0) =
      ⟨[], .torn 0⟩ :=
  scan_stop_first _ .unterminated (next_zeros .format rfl n h0 hn) rfl
    (by simp only [List.length_append, List.length_take, List.length_replicate]
        rw [← format_encode_length]; omega)

/-- And so does one whose format record the crash cut after its length and filled with anything
not ending in the end mark. -/
theorem scan_torn_format_fill (n : Nat) (h4 : 4 ≤ n) (z : Bytes) (b : Byte)
    (hz : n + z.length + 1 = Record.format.encode.length) (hb : b ≠ endMark) :
    scan (Record.format.encode.take n ++ z ++ [b]) = ⟨[], .torn 0⟩ :=
  scan_stop_first _ .unterminated (next_fill .format rfl n h4 z b hz hb) rfl
    (by simp only [List.length_append, List.length_take, List.length_singleton]
        rw [← format_encode_length]; omega)

/-! ## Every rule of reading matters -/

/-- A version of the rules of reading with one of them changed. -/
inductive Mutant
  | none
  /-- the CRC-32C not checked -/
  | crcUnchecked
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
  /-- a journal that need not begin with its format -/
  | formatNotFirst
  /-- the format more than once -/
  | formatAgain
  /-- octets after a commit let be -/
  | inexact
  /-- a commit a correct store does not write taken -/
  | unchecked
  /-- a frame that checks but holds no record taken for a torn tail -/
  | notARecordTorn
  deriving DecidableEq

def rulesOf : Mutant → Rules
  | .none => spec
  | .crcUnchecked => { crc := false }
  | .tornLonger => { maxFrame := maxFrame + 1 }
  | .tornShorter => { maxFrame := maxFrame - 1 }
  | .lengthLonger => { maxPayload := maxPayload + 1 }
  | .lengthShorter => { maxPayload := maxPayload - 1 }
  | .endUnchecked => { ended := false }
  | .tornAtStart => { firstFrame := maxFrame }
  | .formatNotFirst => { formatFirst := false }
  | .formatAgain => { formatOnce := false }
  | .inexact => { exact := false }
  | .unchecked => { checked := false }
  | .notARecordTorn => { strict := false }

def names : List (String × Mutant) :=
  [("crc-unchecked", .crcUnchecked), ("torn-longer", .tornLonger),
   ("torn-shorter", .tornShorter), ("length-longer", .lengthLonger),
   ("length-shorter", .lengthShorter), ("end-unchecked", .endUnchecked),
   ("torn-at-start", .tornAtStart), ("format-not-first", .formatNotFirst),
   ("format-again", .formatAgain), ("inexact", .inexact), ("unchecked", .unchecked),
   ("not-a-record-torn", .notARecordTorn)]

/-- A commit for the examples. -/
def sample : Commit :=
  ⟨1, ascii "<a@b.example>", [⟨ascii "local.test", 1⟩], 100, 200, 12345⟩

/-- A journal that tells the rules with one changed from the rules. None makes the kernel compute
a CRC-32C over more than a small frame. -/
def witness : Mutant → Bytes
  | .none => encodeAll [.format]
  | .crcUnchecked =>
    let j := encodeAll [.format, .commit sample]
    j.set (j.length - 20) (BitVec.ofNat 8 120)
  | .tornLonger => encodeAll [.format] ++ List.replicate (maxFrame + 1) 0
  | .tornShorter => encodeAll [.format] ++ List.replicate maxFrame 0
  | .lengthLonger => encodeAll [.format] ++ le 4 (maxPayload + 1) ++ List.replicate (maxFrame + 1) 0
  | .lengthShorter => encodeAll [.format] ++ le 4 maxPayload ++ List.replicate (maxFrame + 1) 0
  | .endUnchecked => encodeAll [.format] ++ ((Record.commit sample).encode.dropLast ++ [0])
  | .tornAtStart => List.replicate (firstFrame + 1) 0
  | .formatNotFirst => encodeAll [.commit sample]
  | .formatAgain => encodeAll [.format, .format]
  | .inexact => encodeAll [.format] ++ frame commitType (sample.payload ++ [0])
  | .unchecked => encodeAll [.format] ++ frame commitType { sample with messageId := [] }.payload
  | .notARecordTorn => encodeAll [.format] ++ frame 3 sample.payload

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
theorem parseName_names (seq : Nat) (h : seq < 2 ^ 64) :
    parseName journalName = some .journal ∧ parseName (finalName seq) = some (.final seq) ∧
      parseName (tempName seq) = some (.temp seq) := by
  refine ⟨by decide, ?_, ?_⟩ <;>
  · have hl : (hex16 seq).length = 16 := hexOf_length _ _
    simp only [parseName, finalName, tempName, journalName]
    rw [if_neg (by intro e; rw [beq_iff_eq] at e; have := congrArg List.length e
                   simp [ascii, hl] at this)]
    simp [ascii, hexValue_hex16 seq h]

/-- **Different articles get different names**, their numbers below 2 ^ 64. -/
theorem names_injective (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (finalName a = finalName b → a = b) ∧ (tempName a = tempName b → a = b) := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h1 := (parseName_names a ha).2.1
    rw [e, (parseName_names b hb).2.1] at h1
    exact (Name.final.inj (Option.some.inj h1)).symm
  · have h1 := (parseName_names a ha).2.2
    rw [e, (parseName_names b hb).2.2] at h1
    exact (Name.temp.inj (Option.some.inj h1)).symm

end DN.News.Journal
