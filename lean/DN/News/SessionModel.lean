-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.SessionMutant
import DN.News.FrameModel
import DN.News.RecoveryModel

/-!
# DN.News.SessionModel

The session of `DN.News.SessionSpec` run as a program, for a host simulator to drive a line at a
time and for the compiled server to be held against. Its input, blank lines aside:

    identity REVISION SOURCE          both in hex, once, first
    store GROUPS PATH RUN PLACE GEN JOB IMAGE
                                      a store, once, next: the groups (`HEX,HEX`), the path
                                      identity, the run's eight octets, the journal's place and
                                      generation, the last job's generation, and the spool as
                                      recovered (`NAME=OCTETS;…`, as `recovery-model` reads it)
    turn NOW [WALL]                   a batch begins at this time, the wall clock WALL
    open IDX GEN [1] | recv IDX GEN HEX | writable IDX GEN | end IDX GEN | closed IDX GEN
                                      an event; `1` when the connection may post
    complete SLOT GEN OK RESULTS [DATA]
                                      a job's completion: the operations that succeeded, each's
                                      two result words (`A:B,…`, `-` for none), the octets read
    go                                the batch is complete
    took N ...                        what the host took of each send, in order

To `go` it answers the actions, one a line, then the jobs, then `done`:

    send IDX GEN HEX READ | graceful IDX GEN | close IDX GEN
    job SLOT GEN OP …                 `create:NAME`, `write:PLACE:GEN:OFFSET:HEX`,
                                      `datasync:PLACE:GEN`, `close:PLACE:GEN`, `rename:NAME:NAME`,
                                      `remove:NAME`, `syncdir`, `open:NAME`,
                                      `read:PLACE:GEN:OFFSET:LENGTH`

and to `took` the time it needs its next turn, `deadline D`. A report the host may not make is
answered `stop CODE`, after which the model takes no more input. Run with one of the
`DN.News.SessionMutant` rules broken, it is the session the lane has to see is wrong.
-/

namespace DN.News.SessionModel

open DN.News.FrameSpec DN.News.CommandSpec DN.News.SessionSpec DN.News.SessionMutant
open DN.News.FrameModel (parseHex hex)
open DN.News.PostSpec (Store Job Done Op Config)

structure Model where
  mutant : SessionMutant.Mutant := .none
  identity : Option Identity := none
  server : Server := {}
  now : Nat := 0
  wall : Nat := 0
  /-- the events and completions of the batch being read, latest first; `none` between batches -/
  batch : Option (List Event) := none
  dones : List Done := []
  /-- the actions whose sends wait for what the host took -/
  sent : Option (List Action) := none
  stopped : Bool := false

/-- Whether the input may end here: between turns, or after a stop. -/
def Model.atRest (m : Model) : Bool := m.stopped || (m.batch.isNone && m.sent.isNone)

def showAction : Action → String
  | .send idx gen data read =>
    s!"send {idx} {gen} {if data.isEmpty then "-" else hex data} {if read then 1 else 0}"
  | .closeGracefully idx gen => s!"graceful {idx} {gen}"
  | .closeNow idx gen => s!"close {idx} {gen}"

def nameText (n : Journal.Name) : String := String.ofList (n.bytes.map (Char.ofNat ·.toNat))

def showOp : Op → String
  | .create n => s!"create:{nameText n}"
  | .write p g o d => s!"write:{p}:{g}:{o}:{hex d}"
  | .dataSync p g => s!"datasync:{p}:{g}"
  | .close p g => s!"close:{p}:{g}"
  | .rename a b => s!"rename:{nameText a}:{nameText b}"
  | .remove n => s!"remove:{nameText n}"
  | .syncDir => "syncdir"
  | .open_ n => s!"open:{nameText n}"
  | .read p g o l => s!"read:{p}:{g}:{o}:{l}"

def showJob (j : Job) : String := " ".intercalate (s!"job {j.slot} {j.gen}" :: j.ops.map showOp)

/-- A number written in decimal digits and nothing else. -/
def nat (s : String) : Except String Nat :=
  if !s.isEmpty && s.all Char.isDigit then pure s.toNat! else throw s!"not a number: {s}"

def bytes (s : String) : Except String (List Byte) :=
  match parseHex s with
  | some bs => pure bs
  | none => throw s!"not hex: {s}"

def event : List String → Except String Event
  | ["open", i, g] => return .opened (← nat i) (← nat g) false
  | ["open", i, g, "1"] => return .opened (← nat i) (← nat g) true
  | ["recv", i, g, d] => return .received (← nat i) (← nat g) (← bytes d)
  | ["writable", i, g] => return .writable (← nat i) (← nat g)
  | ["end", i, g] => return .inputEnded (← nat i) (← nat g)
  | ["closed", i, g] => return .closed (← nat i) (← nat g)
  | ws => throw s!"not an event: {" ".intercalate ws}"

/-- The two result words of each operation that succeeded. -/
def results (s : String) : Except String (List (Nat × Nat)) :=
  if s == "-" then pure []
  else (s.splitOn ",").mapM fun r =>
    match r.splitOn ":" with
    | [a, b] => return (← nat a, ← nat b)
    | _ => throw s!"not results: {s}"

/-- The run's value as Message-IDs carry it, its octets' hexadecimal digits, and as a number. -/
def runOf (o : List Byte) : List Byte × Nat :=
  (ascii (hex o), o.foldl (fun n b => 256 * n + b.toNat) 0)

/-- The store a recovered spool starts, or why the line gives none. -/
def storeOf (m : SessionMutant.Mutant) (ws : List String) : Except String Store := do
  let [gs, path, run, place, gen, job, image] := ws | throw "not a store"
  let some groups := (RecoveryModel.items "," gs).bind (·.mapM parseHex) | throw "not groups"
  let identity ← bytes path
  let value ← bytes run
  if value.length != 8 then throw "a run's value of eight octets"
  let (random, number) := runOf value
  let cfg : Config := ⟨groups, identity, random, number⟩
  let ctx : ArticleSpec.Context := ⟨groups, identity, 0, 1, random, number, 1⟩
  if !ctx.ok then throw "a configuration the store refuses"
  let some img := RecoveryModel.parseImage image | throw "not an image"
  match Recovery.recover ⟨groups, List.replicate 16 0⟩ img with
  | .ok (st, []) => return Store.start (rulesOf m) cfg st (← nat place, ← nat gen) (← nat job)
  | .ok _ => throw "a spool recovery has more to do in"
  | .error _ => throw "a spool recovery refuses"

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
  | "store" :: ws, some _, none, none =>
    if m.server.store.isSome || m.server.clock != 0 || m.now != 0 then throw "a store after a turn"
    return ({ m with server := { m.server with store := some (← storeOf m.mutant ws) } }, "")
  | ["turn", n], some _, none, none => return ({ m with now := ← nat n, batch := some [] }, "")
  | ["turn", n, w], some _, none, none =>
    return ({ m with now := ← nat n, wall := ← nat w, batch := some [] }, "")
  | ["complete", slot, gen, ok, rs], some _, some _, none =>
    let d : Done := ⟨← nat slot, ← nat gen, ← nat ok, ← results rs, []⟩
    return ({ m with dones := d :: m.dones }, "")
  | ["complete", slot, gen, ok, rs, data], some _, some _, none =>
    let d : Done := ⟨← nat slot, ← nat gen, ← nat ok, ← results rs, ← bytes data⟩
    return ({ m with dones := d :: m.dones }, "")
  | ["go"], some i, some evs, none =>
    match turnM m.mutant i m.server m.now m.wall evs.reverse m.dones.reverse with
    | .error b => return ({ m with stopped := true }, s!"stop {b.code}\n")
    | .ok (s, acts, js) =>
      return ({ m with server := s, batch := none, dones := [], sent := some acts },
        String.join (acts.map (showAction · ++ "\n")) ++
          String.join (js.map (showJob · ++ "\n")) ++ "done\n")
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

/-- Whether `marks` appear in `out` one after another. -/
def inOrder (out : String) : List String → Bool
  | [] => true
  | m :: ms =>
    match out.splitOn m with
    | _ :: rest@(_ :: _) => inOrder (m.intercalate rest) ms
    | _ => false

/-- A POST on an empty spool, each job completing at the next turn: 340; the file created, written,
synced and closed, renamed and the directory synced, the commit appended and the journal synced;
then 240. -/
def regression_961 : Bool :=
  let key := (List.range 16).map (BitVec.ofNat 8)
  let image := hex Journal.journalName ++ "=" ++ hex (Journal.journal key [.start])
  let article := ascii ("From: a@b.example\r\nNewsgroups: local.test\r\nSubject: hi\r\n" ++
    "Message-ID: <r@x.example>\r\n\r\nbody\r\n.\r\n")
  let lines := [identityLine,
    s!"store {hex (ascii "local.test")} {hex (ascii "dn.example")} 0011223344556677 1 0 7 {image}",
    "turn 1 1790000000001", "open 0 1 1", "go", s!"took {(greetingPost exampleIdentity).length}",
    "turn 5 1790000000005", "recv 0 1 " ++ hex (ascii "POST\r\n"), "go",
    s!"took {(text exampleIdentity .post).length}",
    "turn 6 1790000000006", "recv 0 1 " ++ hex article, "go", "took 0",
    "turn 7 1790000000007", "complete 0 8 1 2:0", "go", "took",
    "turn 8 1790000000008", "complete 0 9 3 0:0,0:0,0:0", "go", "took",
    "turn 9 1790000000009", "complete 0 10 2 0:0,0:0", "go", "took",
    "turn 10 1790000000010", "complete 0 11 2 0:0,0:0", "go", "took 25"]
  match runLines lines with
  | .ok out => inOrder out [s!"send 0 1 {hex (text exampleIdentity .post)} 1",
      "job 0 8 create:t0000000000000001", "job 0 9 write:2:0:0:", "datasync:2:0 close:2:0",
      "job 0 10 rename:t0000000000000001:a0000000000000001 syncdir", "job 0 11 write:1:0:",
      "datasync:1:0", s!"send 0 1 {hex (text exampleIdentity .posted)} 1"]
  | .error _ => false

/-- An ARTICLE of an article on the spool, each job completing at the next turn: the file opened,
read with one octet more than it holds and closed in one job; then 220, the header section, Xref,
the body and the dot in one send, the read over, so the host told to read again. -/
def regression_968 : Bool :=
  let key := (List.range 16).map (BitVec.ofNat 8)
  let file := ascii "From: a@b.example\r\nSubject: s\r\n\r\nbody\r\n"
  let c : Journal.Commit :=
    ⟨1, ascii "<1@x.example>", [⟨ascii "local.test", 1⟩], 31, file.length, (Journal.crc32c file).toNat⟩
  let image := hex Journal.journalName ++ "=" ++ hex (Journal.journal key [.commit c, .start]) ++ ";" ++
    hex (Journal.Name.final 1).bytes ++ "=" ++ hex file
  let sent := ascii ("220 0 <1@x.example>\r\nFrom: a@b.example\r\nSubject: s\r\n" ++
    "Xref: dn.example local.test:1\r\n\r\nbody\r\n.\r\n")
  let lines := [identityLine,
    s!"store {hex (ascii "local.test")} {hex (ascii "dn.example")} 0011223344556677 1 0 7 {image}",
    "turn 1 1790000000001", "open 0 1", "go", s!"took {(greeting exampleIdentity).length}",
    "turn 5 1790000000005", "recv 0 1 " ++ hex (ascii "ARTICLE <1@x.example>\r\n"), "go", "took 0",
    "turn 6 1790000000006", "complete 0 8 1 2:0", "go", "took",
    "turn 7 1790000000007", s!"complete 0 9 2 {file.length}:0,0:0 {hex file}", "go", s!"took {sent.length}"]
  match runLines lines with
  | .ok out => inOrder out ["job 0 8 open:a0000000000000001",
      s!"job 0 9 read:2:0:0:{file.length + 1} close:2:0", s!"send 0 1 {hex sent} 1"]
  | .error _ => false

end DN.News.SessionModel
