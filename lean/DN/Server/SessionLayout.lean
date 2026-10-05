-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleSpec
import DN.News.Journal
import DN.News.SessionSpec

/-!
# DN.Server.SessionLayout

Where the session's program (`DN.Server.Session`) keeps what it exchanges with its host and what
it keeps for itself, as offsets from `@base`, and the codes of events, actions, file jobs and stops
(docs/decisions/0003-nntp-slice.md, 0005-article-store.md). `dn-compiler emit-session-layout`
prints them as a C header for the host, so the two cannot disagree about them.

The first 64 bytes of the heap are left to the header the host writes before the program starts.
The offset of every word is a multiple of eight, so a word lies on a word boundary whenever
`@base` does. The sizes are the specification's (`DN.News.SessionSpec`).

- The configuration of both calls: the version word.
- The array `dn_next` fills: first the time the program asks to be woken at (it writes that word
  before the call; zero for none), then the number of events, the host's clock in milliseconds,
  the revision and the address of the source the replies name (a length, then the bytes), the wall
  clock (milliseconds since 1970, UTC), the run's random octets, the path identity and the groups
  (a count, then each a length and the name); the events, each a kind, an index, a generation, a
  length, whether the connection may post, and the bytes; then the number of completions and a
  slot per file job, kind zero if none: a kind, the job's generation, the operations that
  succeeded, the error's class, two result words per operation, and the bytes read.
- The array `dn_emit` hands over: the number of actions, then a slot for each connection, which
  holds its action if it has one and kind zero if not: a kind, an index, a generation, a length,
  whether to read once the bytes are taken, how many of them the kernel took (written back by the
  host), and the bytes; then a slot per file job, kind zero if none: a kind, the job's generation,
  the number of operations, the operations, and the data.
- The program's own area: the host's clock at the last batch, whether the identity was taken in,
  the code the program stopped with, its copy of the identity, the fixed texts of the replies, and
  the table of connections.
-/

namespace DN.Server.SessionLayout

open DN.News.CommandSpec

def version : Nat := 4
/-- The heap the host provisions for the program, from `@base`: 4 MiB (decision 0005). -/
def heapBytes : Nat := 4 * 2 ^ 20
/-- Events in one batch. -/
def batch : Nat := News.SessionSpec.batch
/-- Connections, and actions in one batch. -/
def conns : Nat := News.SessionSpec.conns
/-- Bytes in one event or one action. -/
def data : Nat := News.SessionSpec.chunk
/-- The longest revision and address of the source that fit the replies (`Identity.ok`). -/
def revMax : Nat := 64
def srcMax : Nat := 200

def confOff : Nat := 64
def confLen : Nat := 8

def nextOff : Nat := 128
/-- Within the `dn_next` array. -/
def nextWake : Nat := 0
def nextCount : Nat := 8
def nextClock : Nat := 16
def nextRevLen : Nat := 24
def nextRev : Nat := 32
def nextSrcLen : Nat := nextRev + revMax
def nextSrc : Nat := nextSrcLen + 8
/-- The run's random octets: the value Message-IDs carry, then the key a journal the program
creates is tagged under. -/
def runValueLen : Nat := 8
def randomLen : Nat := runValueLen + News.Journal.keyLength
/-- The longest path identity and group name, and the most groups (`ArticleSpec.Context.ok`). -/
def identityMax : Nat := 200
def groupMax : Nat := 64
def groupsMax : Nat := 64
def nextWall : Nat := nextSrc + srcMax
def nextRandom : Nat := nextWall + 8
def nextIdentityLen : Nat := nextRandom + randomLen
def nextIdentity : Nat := nextIdentityLen + 8
def nextGroupCount : Nat := nextIdentity + identityMax
def nextGroups : Nat := nextGroupCount + 8
/-- A group: its length, then its name. -/
def groupSlot : Nat := 8 + groupMax
def nextEvents : Nat := nextGroups + groupsMax * groupSlot
/-- An event: kind, index, generation, length, whether the connection may post, then the bytes. -/
def eventKind : Nat := 0
def eventIdx : Nat := 8
def eventGen : Nat := 16
def eventLen : Nat := 24
def eventPost : Nat := 32
def eventHead : Nat := 40
def eventSlot : Nat := eventHead + data

/-- File jobs in flight, operations in a job, octets a job moves, and files open at once
(decision 0005: four POSTs, the journal, eight reads and room to spare). -/
def jobs : Nat := 8
def jobOps : Nat := 8
def jobData : Nat := 16384
def handles : Nat := 16

def nextDoneCount : Nat := nextEvents + batch * eventSlot
def nextDone : Nat := nextDoneCount + 8
/-- A completion: kind, the job's generation, how many operations succeeded, the error's class,
two result words for each operation, then the bytes read. -/
def doneKind : Nat := 0
def doneGen : Nat := 8
def doneOps : Nat := 16
def doneClass : Nat := 24
def doneResults : Nat := 32
def doneHead : Nat := doneResults + jobOps * 16
def doneSlot : Nat := doneHead + jobData
def nextLen : Nat := nextDone + jobs * doneSlot

def emitOff : Nat := nextOff + nextLen
/-- Within the `dn_emit` array: the number of actions, then a slot for each connection. -/
def emitCount : Nat := 0
def emitActions : Nat := 8
/-- An action: kind, index, generation, length, whether to read, how many bytes were taken. -/
def actionKind : Nat := 0
def actionIdx : Nat := 8
def actionGen : Nat := 16
def actionLen : Nat := 24
def actionRead : Nat := 32
def actionTaken : Nat := 40
def actionHead : Nat := 48
def actionSlot : Nat := actionHead + data
def emitJobs : Nat := emitActions + conns * actionSlot
/-- A job: kind, its generation, the number of operations, the operations, then its data. -/
def jobKind : Nat := 0
def jobGen : Nat := 8
def jobCount : Nat := 16
def jobOpsAt : Nat := 24
/-- An operation: its code, a file's place and generation, a name's kind and number, a second
name's, an offset, a length, and where its bytes lie in the job's data. -/
def opCode : Nat := 0
def opHandle : Nat := 8
def opHandleGen : Nat := 16
def opName : Nat := 24
def opNumber : Nat := 32
def opToName : Nat := 40
def opToNumber : Nat := 48
def opOffset : Nat := 56
def opLength : Nat := 64
def opData : Nat := 72
def opSlot : Nat := 80
def jobHead : Nat := jobOpsAt + jobOps * opSlot
def jobSlot : Nat := jobHead + jobData
def emitLen : Nat := emitJobs + jobs * jobSlot

def ownOff : Nat := emitOff + emitLen
/-- Within the program's own area. -/
def ownClock : Nat := 0
def ownReady : Nat := 8
def ownStop : Nat := 16
def ownRevLen : Nat := 24
def ownRev : Nat := 32
def ownSrcLen : Nat := ownRev + revMax
def ownSrc : Nat := ownSrcLen + 8
def ownTexts : Nat := ownSrc + srcMax

/-- The fixed texts the replies are made of, and the names of the commands, in the order they lie
from `ownTexts`. -/
def texts : List (List (BitVec 8)) :=
  [greetingHead, greetingMid, crlf, capabilitiesHead, blockEnd, helpHead, helpMid,
   text ⟨[], []⟩ .quit, text ⟨[], []⟩ .noGroup, text ⟨[], []⟩ .noSuchId,
   text ⟨[], []⟩ .unknown, text ⟨[], []⟩ .syntax,
   ascii "CAPABILITIES", ascii "HELP", ascii "QUIT", ascii "HEAD", ascii "STAT"]

/-- Where the `k`-th text starts, from `ownTexts`. -/
def textAt (k : Nat) : Nat := ((texts.take k).map List.length).sum

/-- Rounded up to a multiple of eight. -/
def align8 (k : Nat) : Nat := (k + 7) / 8 * 8

def tableOff : Nat := align8 (ownOff + ownTexts + textAt texts.length)

/-- The words of the framer's block before the bytes of the line it keeps
(`DN.News.FramerProg.lineFrag`). -/
def framerHead : Nat := 40

/-- A connection's record: whether it is in use, its generation, its phase (open, quitting,
ending), whether the last action asked to read, whether a send waits for the host to report the
connection ready, the three deadlines, how many bytes are to send, the held input's end and the
position it is framed to, whether it has an action in the turn, the framer's block, the held
input, and the output. -/
def cLive : Nat := 0
def cGen : Nat := 8
def cPhase : Nat := 16
def cReading : Nat := 24
def cBlocked : Nat := 32
def cFirst : Nat := 40
def cIdle : Nat := 48
def cLineDue : Nat := 56
def cOutLen : Nat := 64
def cHeldLen : Nat := 72
def cHeldPos : Nat := 80
def cActed : Nat := 88
def cFramer : Nat := 96
def cHeld : Nat := cFramer + framerHead + News.SessionSpec.lineLimit
def cOut : Nat := cHeld + data
def connSlot : Nat := cOut + data

/-- The bytes of heap the program needs from `@base`. -/
def size : Nat := tableOff + conns * connSlot

/-- Event kinds. -/
def opened : Nat := 1
def received : Nat := 2
def writable : Nat := 3
def inputEnded : Nat := 4
def closed : Nat := 5

/-- Action kinds. -/
def send : Nat := 1
def closeGracefully : Nat := 2
def closeNow : Nat := 3

/-- A job slot that holds a job, and a completion slot that holds a completion. -/
def job : Nat := 1
def done : Nat := 1

/-- Operation codes (decision 0005). Creating or opening gives a file's place and generation as
its result words. -/
def opCreate : Nat := 1
def opOpen : Nat := 2
def opWrite : Nat := 3
def opRead : Nat := 4
def opSize : Nat := 5
def opDataSync : Nat := 6
def opSync : Nat := 7
def opRename : Nat := 8
def opRemove : Nat := 9
def opTruncate : Nat := 10
def opSyncDir : Nat := 11
def opOpenDir : Nat := 12
def opList : Nat := 13
def opClose : Nat := 14

/-- The class of the error that stopped a job (decision 0005). -/
def classIo : Nat := 1
def classNoSpace : Nat := 2
def classExists : Nat := 3
def classNotFound : Nat := 4
def classOther : Nat := 5

/-- Kinds of name, each made with a number as `DN.News.Journal` makes it. -/
def nameJournal : Nat := 1
def nameFinal : Nat := 2
def nameTemp : Nat := 3
def nameQuarantine : Nat := 4
def nameTail : Nat := 5

/-- The codes of a stop that the host is to blame for: those of `DN.News.SessionSpec.Breach`, then
an event of no kind the layout has, an identity that does not fit the replies, and a word of the
program's own area out of the range the program keeps it in, which a host that writes only into
the arrays of its calls is not seen to cause. -/
def unknownEvent : Nat := 8
def badIdentity : Nat := 9
def brokenState : Nat := 10

def nextName : String := "dn_next"
def emitName : String := "dn_emit"

/-- The layout as a C header. -/
def header : String :=
  let defs : List (String × Nat) :=
    [("VERSION", version), ("BATCH", batch), ("CONNS", conns), ("DATA", data),
     ("REV_MAX", revMax), ("SRC_MAX", srcMax), ("CONF_OFF", confOff), ("CONF_LEN", confLen),
     ("NEXT_OFF", nextOff), ("NEXT_WAKE", nextWake), ("NEXT_COUNT", nextCount),
     ("NEXT_CLOCK", nextClock), ("NEXT_REV_LEN", nextRevLen), ("NEXT_REV", nextRev),
     ("NEXT_SRC_LEN", nextSrcLen), ("NEXT_SRC", nextSrc), ("NEXT_EVENTS", nextEvents),
     ("EVENT_KIND", eventKind), ("EVENT_IDX", eventIdx), ("EVENT_GEN", eventGen),
     ("EVENT_LEN", eventLen), ("EVENT_HEAD", eventHead), ("EVENT_SLOT", eventSlot),
     ("NEXT_LEN", nextLen), ("EMIT_OFF", emitOff), ("EMIT_COUNT", emitCount),
     ("EMIT_ACTIONS", emitActions), ("ACTION_KIND", actionKind), ("ACTION_IDX", actionIdx),
     ("ACTION_GEN", actionGen), ("ACTION_LEN", actionLen), ("ACTION_READ", actionRead),
     ("ACTION_TAKEN", actionTaken), ("ACTION_HEAD", actionHead), ("ACTION_SLOT", actionSlot),
     ("EMIT_LEN", emitLen), ("OWN_OFF", ownOff), ("OWN_STOP", ownStop), ("TABLE_OFF", tableOff),
     ("CONN_SLOT", connSlot), ("C_OUT_LEN", cOutLen), ("C_HELD_LEN", cHeldLen),
     ("C_HELD_POS", cHeldPos), ("C_ACTED", cActed), ("C_FRAMER", cFramer),
     ("OWN_REV_LEN", ownRevLen), ("OWN_SRC_LEN", ownSrcLen), ("SIZE", size),
     ("OPENED", opened), ("RECEIVED", received), ("WRITABLE", writable),
     ("INPUT_ENDED", inputEnded), ("CLOSED", closed), ("SEND", send),
     ("CLOSE_GRACEFULLY", closeGracefully), ("CLOSE_NOW", closeNow),
     ("OVER_TAKEN", News.SessionSpec.Breach.overTaken.code), ("UNKNOWN_EVENT", unknownEvent),
     ("BAD_IDENTITY", badIdentity), ("BROKEN_STATE", brokenState),
     ("HEAP_BYTES", heapBytes), ("RUN_VALUE_LEN", runValueLen), ("RANDOM_LEN", randomLen),
     ("IDENTITY_MAX", identityMax), ("GROUP_MAX", groupMax), ("GROUPS_MAX", groupsMax),
     ("NEXT_WALL", nextWall), ("NEXT_RANDOM", nextRandom), ("NEXT_IDENTITY_LEN", nextIdentityLen),
     ("NEXT_IDENTITY", nextIdentity), ("NEXT_GROUP_COUNT", nextGroupCount),
     ("NEXT_GROUPS", nextGroups), ("GROUP_SLOT", groupSlot), ("EVENT_POST", eventPost),
     ("JOBS", jobs), ("JOB_OPS", jobOps), ("JOB_DATA", jobData), ("HANDLES", handles),
     ("NEXT_DONE_COUNT", nextDoneCount), ("NEXT_DONE", nextDone), ("DONE_KIND", doneKind),
     ("DONE_GEN", doneGen), ("DONE_OPS", doneOps), ("DONE_CLASS", doneClass),
     ("DONE_RESULTS", doneResults), ("DONE_HEAD", doneHead), ("DONE_SLOT", doneSlot),
     ("EMIT_JOBS", emitJobs), ("JOB_KIND", jobKind), ("JOB_GEN", jobGen), ("JOB_COUNT", jobCount),
     ("JOB_OPS_AT", jobOpsAt), ("OP_CODE", opCode), ("OP_HANDLE", opHandle),
     ("OP_HANDLE_GEN", opHandleGen), ("OP_NAME", opName), ("OP_NUMBER", opNumber),
     ("OP_TO_NAME", opToName), ("OP_TO_NUMBER", opToNumber), ("OP_OFFSET", opOffset),
     ("OP_LENGTH", opLength), ("OP_DATA", opData), ("OP_SLOT", opSlot), ("JOB_HEAD", jobHead),
     ("JOB_SLOT", jobSlot), ("JOB", job), ("DONE", done), ("OP_CREATE", opCreate),
     ("OP_OPEN", opOpen), ("OP_WRITE", opWrite), ("OP_READ", opRead), ("OP_SIZE", opSize),
     ("OP_DATA_SYNC", opDataSync), ("OP_SYNC", opSync), ("OP_RENAME", opRename),
     ("OP_REMOVE", opRemove), ("OP_TRUNCATE", opTruncate), ("OP_SYNC_DIR", opSyncDir),
     ("OP_OPEN_DIR", opOpenDir), ("OP_LIST", opList), ("OP_CLOSE", opClose),
     ("CLASS_IO", classIo), ("CLASS_NO_SPACE", classNoSpace), ("CLASS_EXISTS", classExists),
     ("CLASS_NOT_FOUND", classNotFound), ("CLASS_OTHER", classOther),
     ("NAME_JOURNAL", nameJournal), ("NAME_FINAL", nameFinal), ("NAME_TEMP", nameTemp),
     ("NAME_QUARANTINE", nameQuarantine), ("NAME_TAIL", nameTail)]
  "/* Generated by dn-compiler emit-session-layout from DN.Server.SessionLayout. */\n" ++
  "#ifndef DN_SESSION_LAYOUT_H\n#define DN_SESSION_LAYOUT_H\n" ++
  String.join (defs.map fun (name, value) => s!"#define DN_SESSION_{name} {value}\n") ++
  "#endif\n"

/-- The areas stay clear of the heap header, do not overlap, and each word of them is aligned. -/
theorem areas_disjoint :
    64 ≤ confOff ∧ confOff + confLen ≤ nextOff ∧ nextOff + nextLen ≤ emitOff ∧
      emitOff + emitLen ≤ ownOff ∧ ownOff + ownTexts + textAt texts.length ≤ tableOff := by
  decide +kernel

theorem offsets_aligned :
    confOff % 8 = 0 ∧ nextOff % 8 = 0 ∧ nextSrcLen % 8 = 0 ∧ nextEvents % 8 = 0 ∧
      eventSlot % 8 = 0 ∧ emitOff % 8 = 0 ∧ actionSlot % 8 = 0 ∧ ownOff % 8 = 0 ∧
      ownSrcLen % 8 = 0 ∧ ownTexts % 8 = 0 ∧ tableOff % 8 = 0 ∧ connSlot % 8 = 0 ∧
      cFramer % 8 = 0 ∧ nextWall % 8 = 0 ∧ nextIdentityLen % 8 = 0 ∧ nextGroupCount % 8 = 0 ∧
      groupSlot % 8 = 0 ∧ nextDoneCount % 8 = 0 ∧ doneHead % 8 = 0 ∧ doneSlot % 8 = 0 ∧
      emitJobs % 8 = 0 ∧ opSlot % 8 = 0 ∧ jobHead % 8 = 0 ∧ jobSlot % 8 = 0 := by
  decide +kernel

/-- The layout, with the header before it, fits the heap the host provisions. -/
theorem size_fits : size ≤ heapBytes := by decide +kernel

/-- Whatever configuration the article's rules accept fits the places the layout gives it. -/
theorem context_fits (ctx : News.ArticleSpec.Context) (h : ctx.ok = true) :
    ctx.identity.length ≤ identityMax ∧ ctx.groups.length ≤ groupsMax ∧
      ∀ g ∈ ctx.groups, g.length ≤ groupMax := by
  simp only [News.ArticleSpec.Context.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.2, h.1.1.2, fun g hg => (h.2 g hg).1.1⟩

/-- The sizes are those the specification is stated with: an action carries any reply
(`CommandSpec.text_fits`), and a connection holds a line of the limit. -/
theorem sizes_agree :
    data = actionData ∧ cHeld - cFramer - framerHead = News.SessionSpec.lineLimit := by
  decide +kernel

/-- The layout's bounds on the identity are those of `Identity.ok`. -/
theorem identity_ok (i : Identity) :
    i.ok = (1 ≤ i.revision.length && i.revision.length ≤ revMax && i.revision.all isVisible &&
      1 ≤ i.source.length && i.source.length ≤ srcMax && i.source.all isVisible) := rfl

end DN.Server.SessionLayout
