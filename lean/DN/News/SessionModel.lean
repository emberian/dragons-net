-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.SessionMutant
import DN.News.FrameModel

/-!
# DN.News.SessionModel

The session of `DN.News.SessionSpec` run as a program, for a host simulator to drive a line at a
time and for the compiled server to be held against. Its input, blank lines aside:

    identity REVISION SOURCE          both in hex, once, first
    turn NOW                          a batch begins at this time
    open IDX GEN | recv IDX GEN HEX | writable IDX GEN | end IDX GEN | closed IDX GEN
    go                                the batch is complete
    took N ...                        what the host took of each send, in order

To `go` it answers the actions, one a line, then `done`:

    send IDX GEN HEX READ | graceful IDX GEN | close IDX GEN

and to `took` the time it needs its next turn, `deadline D`. A report the host may not make is
answered `stop CODE`, after which the model takes no more input. Run with one of the
`DN.News.SessionMutant` rules broken, it is the session the lane has to see is wrong.
-/

namespace DN.News.SessionModel

open DN.News.FrameSpec DN.News.CommandSpec DN.News.SessionSpec DN.News.SessionMutant
open DN.News.FrameModel (parseHex hex)

structure Model where
  mutant : SessionMutant.Mutant := .none
  identity : Option Identity := none
  server : Server := {}
  now : Nat := 0
  /-- the events of the batch being read, latest first; `none` between batches -/
  batch : Option (List Event) := none
  /-- the actions whose sends wait for what the host took -/
  sent : Option (List Action) := none
  stopped : Bool := false

/-- Whether the input may end here: between turns, or after a stop. -/
def Model.atRest (m : Model) : Bool := m.stopped || (m.batch.isNone && m.sent.isNone)

def showAction : Action → String
  | .send idx gen data read =>
    s!"send {idx} {gen} {hex data} {if read then 1 else 0}"
  | .closeGracefully idx gen => s!"graceful {idx} {gen}"
  | .closeNow idx gen => s!"close {idx} {gen}"

/-- A number written in decimal digits and nothing else. -/
def nat (s : String) : Except String Nat :=
  if !s.isEmpty && s.all Char.isDigit then pure s.toNat! else throw s!"not a number: {s}"

def bytes (s : String) : Except String (List Byte) :=
  match parseHex s with
  | some bs => pure bs
  | none => throw s!"not hex: {s}"

def event : List String → Except String Event
  | ["open", i, g] => return .opened (← nat i) (← nat g)
  | ["recv", i, g, d] => return .received (← nat i) (← nat g) (← bytes d)
  | ["writable", i, g] => return .writable (← nat i) (← nat g)
  | ["end", i, g] => return .inputEnded (← nat i) (← nat g)
  | ["closed", i, g] => return .closed (← nat i) (← nat g)
  | ws => throw s!"not an event: {" ".intercalate ws}"

/-- One line of input: the model after it, and what it answers (possibly nothing). -/
def step (m : Model) (line : String) : Except String (Model × String) := do
  let ws := line.splitOn " " |>.filter (· ≠ "")
  if ws.isEmpty then return (m, "")
  if m.stopped then throw "input after a stop"
  match ws, m.identity, m.batch, m.sent with
  | ["identity", r, s], none, none, none =>
    let i : Identity := ⟨← bytes r, ← bytes s⟩
    if !i.ok then throw "an identity that does not fit the replies"
    return ({ m with identity := some i }, "")
  | ["turn", n], some _, none, none => return ({ m with now := ← nat n, batch := some [] }, "")
  | ["go"], some i, some evs, none =>
    match turnM m.mutant i m.server m.now evs.reverse with
    | .error b => return ({ m with stopped := true }, s!"stop {b.code}\n")
    | .ok (s, acts) =>
      return ({ m with server := s, batch := none, sent := some acts },
        String.join (acts.map (showAction · ++ "\n")) ++ "done\n")
  | "took" :: ns, some _, none, some acts =>
    match settleM m.mutant m.server acts (← ns.mapM nat) with
    | .error b => return ({ m with stopped := true }, s!"stop {b.code}\n")
    | .ok s => return ({ m with server := s, sent := none }, s!"deadline {deadlineM m.mutant s}\n")
  | ws, some _, some evs, none => return ({ m with batch := some ((← event ws) :: evs) }, "")
  | _, _, _, _ => throw s!"unexpected: {line}"

/-- The answers to a whole script of lines, as `dn-compiler session-model` gives them. -/
def runLines (lines : List String) : Except String String := do
  let (_, out) ← lines.foldlM (fun (m, out) l => do
      let (m', o) ← step m l
      pure (m', out ++ o)) (({} : Model), "")
  return out

/-- The identity the examples run with. -/
def exampleIdentity : Identity := ⟨ascii "r1", ascii "https://example.org/src"⟩

/-- A connection greeted, then a command and a QUIT in one received chunk: the greeting, then
the capabilities without reading on, then — their output taken — the 205, then the graceful
close. -/
def regression_821 : Bool :=
  let i := exampleIdentity
  let g := greeting i
  let c := text i .capabilities
  let q := text i .quit
  (runLines ["identity " ++ hex i.revision ++ " " ++ hex i.source, "turn 5", "open 3 7", "go",
      s!"took {g.length}", "turn 6", "recv 3 7 " ++ hex (ascii "CAPABILITIES\r\nQUIT\r\n"), "go",
      s!"took {c.length}", "turn 7", "go", s!"took {q.length}", "turn 8", "go", "took"]).toOption ==
    some (s!"send 3 7 {hex g} 1\ndone\ndeadline 10005\n" ++
      s!"send 3 7 {hex c} 0\ndone\ndeadline 6\n" ++
      s!"send 3 7 {hex q} 0\ndone\ndeadline 7\n" ++ "graceful 3 7\ndone\ndeadline 0\n")

/-- The identity line of the examples. -/
def identityLine : String :=
  "identity " ++ hex exampleIdentity.revision ++ " " ++ hex exampleIdentity.source

/-- An index given to a new connection: bytes reported for the old generation are left alone, and
the new one is greeted. -/
def regression_822 : Bool :=
  let g := greeting exampleIdentity
  (runLines [identityLine, "turn 5", "open 0 1", "go", s!"took {g.length}", "turn 6", "closed 0 1",
      "open 0 2", "recv 0 1 " ++ hex (ascii "HELP\r\n"), "go", s!"took {g.length}"]).toOption ==
    some (s!"send 0 1 {hex g} 1\ndone\ndeadline 10005\n" ++
      s!"send 0 2 {hex g} 1\ndone\ndeadline 10006\n")

/-- After the 205 the host was not asked to read; bytes it reports all the same end the run. -/
def regression_823 : Bool :=
  let g := greeting exampleIdentity
  let q := text exampleIdentity .quit
  (runLines [identityLine, "turn 5", "open 0 1", "go", s!"took {g.length}", "turn 6",
      "recv 0 1 " ++ hex (ascii "QUIT\r\n"), "go", s!"took {q.length}", "turn 7",
      "recv 0 1 " ++ hex (ascii "HELP\r\n"), "go"]).toOption ==
    some (s!"send 0 1 {hex g} 1\ndone\ndeadline 10005\n" ++
      s!"send 0 1 {hex q} 0\ndone\ndeadline 6\n" ++ "stop 4\n")

end DN.News.SessionModel
