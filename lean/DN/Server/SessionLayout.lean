-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.ArticleProg
import DN.News.Journal
import DN.News.SessionSpec
import DN.News.RecoverProg

/-!
# DN.Server.SessionLayout

Where the session's program (`DN.Server.Session`) keeps what it exchanges with its host and what
it keeps for itself, as offsets from `@base`, and the codes of events, actions, file jobs and stops
(docs/decisions/0003-nntp-slice.md, 0005-article-store.md). `dn-compiler emit-session-layout`
prints them as a C header for the host, so the two cannot disagree about them.

The first 64 bytes of the heap are left to the header the host writes before the program starts.
The offset of every word is a multiple of eight, so a word lies on a word boundary whenever
`@base` does. The sizes are the specification's (`DN.News.SessionSpec`).

- The area of the grammar's and the article's functions (`DN.News.ArticleProg`), first, where their
  own lane runs them.
- The configuration of both calls: the version word.
- The array `dn_next` fills: first the time the program asks to be woken at (it writes that word
  before the call; zero for none), then the number of events, the host's clock in milliseconds,
  the revision and the address of the source the replies name (a length, then the bytes), whether
  there is a store, the wall clock (milliseconds since 1970, UTC), the run's random octets, the path
  identity and the groups (a count, then each a length and the name); the events, each a kind, an
  index, a generation, a length, whether the connection may post, and the bytes; then the number
  of completions and a slot per file job, kind zero if none: a kind, the job's generation, the
  operations that succeeded, the error's class, two result words per operation, and the bytes
  read.
- The array `dn_emit` hands over: the number of actions, whether the host is to listen (zero until
  the program has recovered its store, then one), then a slot for each connection, which holds its
  action if it has one and kind zero if not: a kind, an index, a generation, a length, whether to
  read once the bytes are taken, how many of them the kernel took (written back by the host), and
  the bytes; then a slot per file job, kind zero if none: a kind, the job's generation,
  the number of operations, the operations, and the data.
- The program's own area: the host's clock at the last batch, whether the identity was taken in,
  the code the program stopped with, its copy of the identity, the store's words, the CRC-32C's
  table, the fixed texts of the replies, and the table of connections; then the area of recovery at
  start (`DN.News.RecoverProg`) and of the file jobs that drive it: the places of the directory's
  listing and of the journal, how far the listing is read, the generation of the last job, the class
  of the error a failed job stopped with, and a page of the listing; then the slots of POSTs
  (`DN.News.PostSpec`) and the index of the Message-IDs the store holds.
-/

namespace DN.Server.SessionLayout

open DN.News.CommandSpec

def version : Nat := 7
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

def artOff : Nat := News.AbnfProg.areaOffset
/-- Past the article's area: `News.ArticleProg.heapSize` (`regression_966`), written out so that the
kernel does not compute the area to check the layout. -/
def confOff : Nat := 579264
def confLen : Nat := 8

def nextOff : Nat := confOff + 64
/-- Within the `dn_next` array. -/
def nextWake : Nat := 0
def nextCount : Nat := 8
def nextClock : Nat := 16
def nextRevLen : Nat := 24
def nextRev : Nat := 32
def nextSrcLen : Nat := nextRev + revMax
def nextSrc : Nat := nextSrcLen + 8
/-- The run's random octets: the value Message-IDs carry, the key a journal the program creates is
tagged under, then the key of the index of Message-IDs (SipHash-2-4's). -/
def runValueLen : Nat := 8
def indexKeyLen : Nat := 16
def randomLen : Nat := runValueLen + News.Journal.keyLength + indexKeyLen
/-- The longest path identity and group name, and the most groups (`ArticleSpec.Context.ok`). -/
def identityMax : Nat := 200
def groupMax : Nat := 64
def groupsMax : Nat := 64
def nextStore : Nat := nextSrc + srcMax
def nextWall : Nat := nextStore + 8
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
(decision 0005: four POSTs, the journal, eight reads and room to spare), as the specification has
them (`DN.News.PostSpec`). -/
def jobs : Nat := News.PostSpec.jobs
def jobOps : Nat := News.PostSpec.jobOps
def jobData : Nat := News.PostSpec.jobData
def handles : Nat := News.PostSpec.places

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
/-- Within the `dn_emit` array: the number of actions, whether the host is to listen, then a slot
for each connection. -/
def emitCount : Nat := 0
def emitListen : Nat := 8
def emitActions : Nat := 16
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
name's, an offset (for a listing, the index of its first name), a length, and where its bytes lie
in the job's data. -/
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
/-- The store: whether there is one, whether it accepts, the next sequence number, where the journal
ends, how many numbers are set aside, the batch's wall clock in seconds; what a function called
last found; the actions of the turn so far; how many connections have opened, the POSTs waiting
for a slot (a count, then an index and a generation each), the journal's key and the index's; a
Message-ID being looked up, a message a tag is made of, and the CRC-32C's table. -/
def ownStore : Nat := ownSrc + srcMax
def ownAccepting : Nat := ownStore + 8
def ownNext : Nat := ownAccepting + 8
def ownJournalEnd : Nat := ownNext + 8
def ownAside : Nat := ownJournalEnd + 8
def ownWall : Nat := ownAside + 8
def ownRet : Nat := ownWall + 8
def ownActs : Nat := ownRet + 8
def ownOpened : Nat := ownActs + 8
def ownWaitN : Nat := ownOpened + 8
def ownWaits : Nat := ownWaitN + 8
def ownKey : Nat := ownWaits + conns * 16
def ownIndexKey : Nat := ownKey + News.Journal.keyLength
def ownId : Nat := ownIndexKey + indexKeyLen
def ownMsg : Nat := ownId + 256
def ownCrc : Nat := ownMsg + (News.Journal.maxFrame + 7) / 8 * 8
def ownTexts : Nat := ownCrc + 256 * 8

/-- The fixed texts the replies are made of, and the names of the commands, in the order they lie
from `ownTexts`. -/
def texts : List (List (BitVec 8)) :=
  [greetingHead, greetingMid, crlf, capabilitiesHead, blockEnd, helpHead, helpMid,
   text ⟨[], []⟩ .quit, text ⟨[], []⟩ .noGroup, text ⟨[], []⟩ .noSuchId,
   text ⟨[], []⟩ .unknown, text ⟨[], []⟩ .syntax,
   ascii "CAPABILITIES", ascii "HELP", ascii "QUIT", ascii "HEAD", ascii "STAT", ascii "POST",
   greetingPostHead, greetingPostMid, capabilitiesPostTail, helpPostHead, text ⟨[], []⟩ .post,
   text ⟨[], []⟩ .posted, text ⟨[], []⟩ .failed, text ⟨[], []⟩ .notPermitted,
   text ⟨[], []⟩ .unavailable]

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
position it is framed to, whether it has an action in the turn, its number among the connections,
whether it was greeted with 200, whether a POST waits, the slot of its POST and one, or zero, the
article's deadline, the framer's block, the held input, and the output. -/
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
def cNumber : Nat := 96
def cGreeted : Nat := 104
def cWaiting : Nat := 112
def cPost : Nat := 120
def cArticleDue : Nat := 128
def cFramer : Nat := 136
def cHeld : Nat := cFramer + framerHead + News.SessionSpec.lineLimit
def cOut : Nat := cHeld + data
def connSlot : Nat := cOut + data

/-- Recovery's area, then the words of the jobs that drive it. -/
def recOff : Nat := tableOff + conns * connSlot
def drvOff : Nat := recOff + News.RecoverProg.size
def dDir : Nat := 0
def dDirGen : Nat := 8
def dDirOpen : Nat := 16
def dJnl : Nat := 24
def dJnlGen : Nat := 32
def dJnlOpen : Nat := 40
def dIndex : Nat := 48
def dPageLen : Nat := 56
def dPagePos : Nat := 64
def dGen : Nat := 72
def dClass : Nat := 80
/-- A page of the listing, with a name's room past it. -/
def dPage : Nat := 88

/-- The slots of POSTs, each the state of `DN.News.PostSpec.Slot`: whether it is in use, its owner
(whether it has one, its index and generation) and the owner's number; the framer's phase and
whether the block is spoiled, the octets arrived, whether the block has ended, whether the header
section has ended, whether the next octet of the file starts a line, whether it is refused and its
outcome (none, posted, failed, lost); its article — whether it has one, its number, the header
section's size in the file, the file's octets so far, how many are written, how many wait to be,
the CRC-32C so far, the file (none, open, closed, final, placed) and its place and generation; its
job in flight — whether it has one, its job slot, generation, operations, task (create, write,
finish, place, commit, clean) and the task's two numbers; the Message-ID's length, the groups (a
count, then each one's index in the configuration), the numbers its commit gives them, the
Message-ID, and the buffer: the header section as it arrives, then the octets of the file not
written. -/
def slotsOff : Nat := drvOff + dPage + jobData + 256
def posts : Nat := ({} : News.PostSpec.Rules).posts
def zLive : Nat := 0
def zOwner : Nat := 8
def zOwnIdx : Nat := 16
def zOwnGen : Nat := 24
def zConn : Nat := 32
def zPh : Nat := 40
def zBad : Nat := 48
def zArrived : Nat := 56
def zEnded : Nat := 64
def zBody : Nat := 72
def zBol : Nat := 80
def zRefused : Nat := 88
def zOutcome : Nat := 96
def zHas : Nat := 104
def zSeq : Nat := 112
def zHeadSize : Nat := 120
def zSize : Nat := 128
def zWritten : Nat := 136
def zPend : Nat := 144
def zCrc : Nat := 152
def zFile : Nat := 160
def zPlace : Nat := 168
def zPGen : Nat := 176
def zBusy : Nat := 184
def zJob : Nat := 192
def zJGen : Nat := 200
def zJOps : Nat := 208
def zTask : Nat := 216
def zTaskA : Nat := 224
def zTaskB : Nat := 232
def zMsgLen : Nat := 240
def zGroupN : Nat := 248
def zGroups : Nat := 256
def zNums : Nat := zGroups + 16 * 8
def zMsg : Nat := zNums + 16 * 8
def zBuf : Nat := zMsg + 256
/-- The buffer holds the header section as it arrives, at most two octets past its bound
(`PostSpec.frameOctet_adds`), and then the octets of the file not written: the header section
stored, each octet stuffed into at most two, and its empty line; or fewer than a job's octets and
what one framed octet adds, stuffed. -/
def bufMax : Nat := 2 * News.ArticleProg.outMax + 8
def slotLen : Nat := zBuf + bufMax

/-- The index: a cell per place, zero or one more than the place of a commit in recovery's area. -/
def indexOff : Nat := slotsOff + posts * slotLen
def indexCells : Nat := 8192

/-- The bytes of heap the program needs from `@base`. -/
def size : Nat := indexOff + indexCells * 8

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
an event of no kind the layout has, an identity or groups that do not fit the replies or the
store, and a word of the program's own area out of the range the program keeps it in, which a host
that writes only into the arrays of its calls is not seen to cause. -/
def unknownEvent : Nat := 8
def badIdentity : Nat := 9
def brokenState : Nat := 10
/-- The codes of a stop at start: recovery refuses the store, or a file job it drove failed. -/
def storeRefused : Nat := 11
def recoveryFailed : Nat := 12

def nextName : String := "dn_next"
def emitName : String := "dn_emit"

/-- The layout as a C header. -/
def header : String :=
  let defs : List (String × Nat) :=
    [("VERSION", version), ("BATCH", batch), ("CONNS", conns), ("DATA", data), ("ART_OFF", artOff),
     ("REV_MAX", revMax), ("SRC_MAX", srcMax), ("CONF_OFF", confOff), ("CONF_LEN", confLen),
     ("NEXT_OFF", nextOff), ("NEXT_WAKE", nextWake), ("NEXT_COUNT", nextCount),
     ("NEXT_CLOCK", nextClock), ("NEXT_REV_LEN", nextRevLen), ("NEXT_REV", nextRev),
     ("NEXT_SRC_LEN", nextSrcLen), ("NEXT_SRC", nextSrc), ("NEXT_EVENTS", nextEvents),
     ("EVENT_KIND", eventKind), ("EVENT_IDX", eventIdx), ("EVENT_GEN", eventGen),
     ("EVENT_LEN", eventLen), ("EVENT_HEAD", eventHead), ("EVENT_SLOT", eventSlot),
     ("NEXT_LEN", nextLen), ("EMIT_OFF", emitOff), ("EMIT_COUNT", emitCount),
     ("EMIT_LISTEN", emitListen), ("EMIT_ACTIONS", emitActions), ("ACTION_KIND", actionKind),
     ("ACTION_IDX", actionIdx), ("ACTION_GEN", actionGen), ("ACTION_LEN", actionLen),
     ("ACTION_READ", actionRead),
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
     ("STORE_REFUSED", storeRefused), ("RECOVERY_FAILED", recoveryFailed),
     ("NEXT_STORE", nextStore),
     ("REC_OFF", recOff), ("REC_FAULT", News.RecoverProg.rFault),
     ("REC_FAULT_A", News.RecoverProg.rFaultA), ("REC_FAULT_B", News.RecoverProg.rFaultB),
     ("REC_FAULT_AT", News.RecoverProg.rFaultAt), ("REC_FAULT_LEN", News.RecoverProg.rFaultLen),
     ("REC_NAME", News.RecoverProg.rName), ("REC_NAME_LEN", News.RecoverProg.rNameLen),
     ("REC_AREA", News.RecoverProg.size), ("DRV_OFF", drvOff), ("D_CLASS", dClass),
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
     ("NAME_QUARANTINE", nameQuarantine), ("NAME_TAIL", nameTail),
     ("WALL_LIMIT", News.SessionSpec.wallLimit), ("OWN_STORE", ownStore), ("OWN_WAIT_N", ownWaitN),
     ("OWN_NEXT", ownNext), ("OWN_JOURNAL_END", ownJournalEnd), ("OWN_ACTS", ownActs),
     ("C_POST", cPost),
     ("SLOTS_OFF", slotsOff), ("SLOT_LEN", slotLen), ("POSTS", posts), ("Z_PH", zPh),
     ("Z_PEND", zPend), ("Z_HEAD_SIZE", zHeadSize), ("Z_JOB", zJob), ("Z_GROUP_N", zGroupN),
     ("Z_MSG_LEN", zMsgLen), ("BUF_MAX", bufMax), ("INDEX_OFF", indexOff),
     ("INDEX_CELLS", indexCells)]
  "/* Generated by dn-compiler emit-session-layout from DN.Server.SessionLayout. */\n" ++
  "#ifndef DN_SESSION_LAYOUT_H\n#define DN_SESSION_LAYOUT_H\n" ++
  String.join (defs.map fun (name, value) => s!"#define DN_SESSION_{name} {value}\n") ++
  "#endif\n"

/-- The areas stay clear of the heap header, do not overlap, and each word of them is aligned; the
article's area ends where the configuration starts by `regression_966`. -/
theorem areas_disjoint :
    64 ≤ artOff ∧ confOff + confLen ≤ nextOff ∧ nextOff + nextLen ≤ emitOff ∧
      emitOff + emitLen ≤ ownOff ∧ ownOff + ownTexts + textAt texts.length ≤ tableOff ∧
      drvOff + dPage + jobData + 256 ≤ slotsOff := by
  decide +kernel

theorem offsets_aligned :
    confOff % 8 = 0 ∧ nextOff % 8 = 0 ∧ nextSrcLen % 8 = 0 ∧ nextEvents % 8 = 0 ∧
      eventSlot % 8 = 0 ∧ emitOff % 8 = 0 ∧ actionSlot % 8 = 0 ∧ ownOff % 8 = 0 ∧
      ownSrcLen % 8 = 0 ∧ ownTexts % 8 = 0 ∧ tableOff % 8 = 0 ∧ connSlot % 8 = 0 ∧
      cFramer % 8 = 0 ∧ nextWall % 8 = 0 ∧ nextIdentityLen % 8 = 0 ∧ nextGroupCount % 8 = 0 ∧
      groupSlot % 8 = 0 ∧ nextDoneCount % 8 = 0 ∧ doneHead % 8 = 0 ∧ doneSlot % 8 = 0 ∧
      emitJobs % 8 = 0 ∧ opSlot % 8 = 0 ∧ jobHead % 8 = 0 ∧ jobSlot % 8 = 0 ∧ nextStore % 8 = 0 ∧
      recOff % 8 = 0 ∧ drvOff % 8 = 0 ∧ ownStore % 8 = 0 ∧ ownWaits % 8 = 0 ∧ ownKey % 8 = 0 ∧
      ownId % 8 = 0 ∧ ownMsg % 8 = 0 ∧ ownCrc % 8 = 0 ∧ slotsOff % 8 = 0 ∧ slotLen % 8 = 0 ∧
      zBuf % 8 = 0 ∧ indexOff % 8 = 0 := by
  decide +kernel

/-- The configuration lies past the article's area, which starts where that program's lane has
it. -/
def regression_966 : Bool :=
  artOff == News.AbnfProg.areaOffset && confOff == News.ArticleProg.heapSize

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
