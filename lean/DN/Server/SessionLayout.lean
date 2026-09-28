-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.SessionSpec

/-!
# DN.Server.SessionLayout

Where the session's program (`DN.Server.Session`) keeps what it exchanges with its host and what
it keeps for itself, as offsets from `@base`, and the codes of events, actions and stops
(docs/decisions/0003-nntp-slice.md). `dn-compiler emit-session-layout` prints them as a C header
for the host, so the two cannot disagree about them.

The first 64 bytes of the heap are left to the header the host writes before the program starts.
The offset of every word is a multiple of eight, so a word lies on a word boundary whenever
`@base` does. The sizes are the specification's (`DN.News.SessionSpec`).

- The configuration of both calls: the version word.
- The array `dn_next` fills: first the time the program asks to be woken at (it writes that word
  before the call; zero for none), then the number of events, the host's clock in milliseconds,
  the revision and the address of the source the replies name (a length, then the bytes), then
  the events, each a kind, an index, a generation, a length and the received bytes.
- The array `dn_emit` hands over: the number of actions, then the actions, one for each
  connection at most, each a kind, an index, a generation, a length, whether to read once the
  bytes are taken, how many of them the kernel took (written back by the host), and the bytes.
- The program's own area: the host's clock at the last batch, whether the identity was taken in,
  the code the program stopped with, its copy of the identity, the fixed texts of the replies, and
  the table of connections.
-/

namespace DN.Server.SessionLayout

open DN.News.CommandSpec

def version : Nat := 2
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
def nextEvents : Nat := nextSrc + srcMax
/-- An event: kind, index, generation, length, then the bytes. -/
def eventKind : Nat := 0
def eventIdx : Nat := 8
def eventGen : Nat := 16
def eventLen : Nat := 24
def eventHead : Nat := 32
def eventSlot : Nat := eventHead + data
def nextLen : Nat := nextEvents + batch * eventSlot

def emitOff : Nat := nextOff + nextLen
/-- Within the `dn_emit` array: the number of actions, then the actions. -/
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
def emitLen : Nat := emitActions + conns * actionSlot

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
(`DN.News.FramerCode.lineFrag`). -/
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

/-- The codes of a stop that the host is to blame for: those of `DN.News.SessionSpec.Breach`, then
an event of no kind the layout has, and an identity that does not fit the replies. -/
def unknownEvent : Nat := 8
def badIdentity : Nat := 9

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
     ("EMIT_LEN", emitLen), ("OWN_OFF", ownOff), ("OWN_STOP", ownStop), ("SIZE", size),
     ("OPENED", opened), ("RECEIVED", received), ("WRITABLE", writable),
     ("INPUT_ENDED", inputEnded), ("CLOSED", closed), ("SEND", send),
     ("CLOSE_GRACEFULLY", closeGracefully), ("CLOSE_NOW", closeNow),
     ("OVER_TAKEN", News.SessionSpec.Breach.overTaken.code), ("UNKNOWN_EVENT", unknownEvent),
     ("BAD_IDENTITY", badIdentity)]
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
      cFramer % 8 = 0 := by
  decide +kernel

/-- The layout, with the header before it, fits the heap segment the host provisions (1 MiB). -/
theorem size_fits : size ≤ 2 ^ 20 := by decide +kernel

/-- The sizes are those the specification is stated with: an action carries any reply
(`CommandSpec.text_fits`), and a connection holds a line of the limit. -/
theorem sizes_agree :
    data = actionData ∧ cHeld - cFramer - framerHead = News.SessionSpec.lineLimit := by
  decide +kernel

/-- The identities the program accepts, by its bounds, are those `Identity.ok` accepts. -/
theorem identity_ok (i : Identity) :
    i.ok = (1 ≤ i.revision.length && i.revision.length ≤ revMax && i.revision.all isVisible &&
      1 ≤ i.source.length && i.source.length ≤ srcMax && i.source.all isVisible) := rfl

end DN.Server.SessionLayout
