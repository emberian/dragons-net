-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.AbnfProg
import DN.News.ArticleModel

/-!
# DN.News.ArticleProg

What `DN.News.ArticleSpec.checkWith` says of a proto-article, as Pancake functions over the
grammar's (`DN.News.AbnfProg`): its verdict, the name a refusal gives, and for an article accepted
its header section with what was added, its message identifier and the groups carried that it names.
The functions are made from the rules (`Rules`), so a version of the rules makes a version of them.

The input is the header section the session gathers: the proto-article up to the empty line
after its header, at most `artMax` octets, in the grammar's input, so each field's grammar is
matched where it lies. A pass over the lines finds the empty line and checks the section's shape; a
pass over the fields checks each and notes, for each name the rules read, its first field, and the
first field repeated, with a long message identifier or with a date that means none; then the
article's rules run in the order of `articleRefusal`.

Pancake has no division: a quotient is built bit by bit from the grammar's table of powers of two,
and a decimal digit as `DN.Compiler.Div10` does. A date's year may have any number of digits: its
leap years and days of the week repeat every 400 years, and a year from `yearBig` on is past any
wall clock below `wallMax`, which the program takes. The context is checked on its own, before the
articles, as the session checks its configuration. Tested against `dn-compiler article-model`, not
proven.
-/

namespace DN.News.ArticleProg

open DN.Compiler DN.Compiler.Syntax
open DN.News.AbnfProg (kept areaAt ne or2 inc word byte aInput aLen aBroken pow inputMax rootCall)
open DN.News.ArticleSpec (Rules spec idFields Refusal)

/-- Defects a version of the program may carry, each of which the lane has to see. -/
inductive Mutant
  | none
  /-- a CR ends a line without its LF -/
  | crEndsLine
  /-- a field's name is compared with its case -/
  | caseful
  /-- a date's day of the week is not checked -/
  | weekdayUnchecked
  /-- a long year is taken as `yearBig`, its place in the 400 years lost -/
  | yearShort
  /-- Path is folded one octet before its line reaches the bound -/
  | foldEarly
  /-- in a comment of a field of message identifiers, `\` quotes nothing -/
  | escapeKept
  /-- a copy does not check where it reads, which only the analysis can see -/
  | unkept
  deriving DecidableEq, Inhabited

def mutantNames : List (String × Mutant) :=
  [("cr-ends-line", .crEndsLine), ("caseful", .caseful), ("weekday-unchecked", .weekdayUnchecked),
   ("year-short", .yearShort), ("fold-early", .foldEarly), ("escape-kept", .escapeKept)]

/-- The longest input: a header section at its bound, the octets one framed octet adds past it,
with room. -/
def artMax : Nat := 65600
/-- The longest header section stored: the section at its bound and what is added. -/
def outMax : Nat := 69632
/-- A year from here on is past any wall clock the program takes. -/
def yearBig : Nat := 100000
/-- The wall clocks the program takes are below this, in the year 36,812. -/
def wallMax : Nat := 2 ^ 40

def codes (s : String) : List Nat := s.toList.map Char.toNat
def lowerS (s : String) : String := s.map Char.toLower

/-! ## The names the rules read -/

def dateFields : List String := ["Date", "Injection-Date", "Expires", "Resent-Date"]
def readNames : List String :=
  ["Received", "Path", "Sender", "From", "Distribution", "Newsgroups", "Message-ID"]

/-- Every name the rules give a field, each once, compared without case. -/
def entries (r : Rules) : List String :=
  (r.injected ++ r.traced ++ r.deprecated ++ r.notOffered ++ r.once ++ r.required ++
    AbnfRules.fieldRules.map (·.1) ++ idFields ++ dateFields ++ readNames).foldl
    (fun acc s => if acc.any (lowerS · == lowerS s) then acc else acc ++ [s]) []

def isIn (l : List String) (s : String) : Bool := l.any (lowerS · == lowerS s)

/-- A name's place among the entries; a field of no entry's name is at `es.length`. -/
def entryOf (es : List String) (s : String) : Nat :=
  (es.findIdx? (lowerS · == lowerS s)).getD es.length

/-- What a name is to the rules, a bit each: injected, traced, deprecated, not offered, once, a
field of message identifiers, a field of a date, Received. -/
def flagsOf (r : Rules) (s : String) : Nat :=
  [isIn r.injected s, isIn r.traced s, isIn r.deprecated s, isIn r.notOffered s, isIn r.once s,
   isIn idFields s, isIn dateFields s, lowerS s == "received"].zipIdx.foldl
    (fun acc (b, i) => if b then acc + 2 ^ i else acc) 0

/-- The grammar rule of a field of the name, as `ArticleSpec.ruleOf` finds it. -/
def ruleOfName (s : String) : Nat :=
  ((AbnfRules.fieldRules.find? (lowerS ·.1 == lowerS s)).map (·.2)).getD AbnfRules.optionalField

/-! ## The area

The grammar's area, then the article's: the request and the context; the verdict and what an
accepted article gets; the words the functions hand each other; the groups, the identity, the
random value, the name of a refusal, the message identifier, scratch; the header section made;
the entries' tables. -/

def X : Nat := AbnfProg.size
def w (i : Nat) : Nat := X + 8 * i
def xMode := w 0
def xLen := w 1
def xWall := w 2
def xSeq := w 3
def xRun := w 4
def xConn := w 5
def xIdLen := w 6
def xRandLen := w 7
def xGroupsN := w 8
def xCtxOk := w 9
def xVerdict := w 10
def xNameLen := w 11
def xOutLen := w 12
def xMsgLen := w 13
def xKnownN := w 14
def xValue := w 15
def xSep := w 16
def xNl := w 17
def xE1 := w 18
def xTokS := w 19
def xTokLen := w 20
def xElemLen := w 21
def xElemRes := w 22
def xMsgS := w 23
def xMsgL := w 24
def xNumMod := w 25
def xGCount := w 26
def xGRes := w 27
def xGKnown := w 28
def xKnown := w 32
def knownMax : Nat := 64
/-- A group: its length, then room for one past the bound. -/
def groupSize : Nat := 80
def groupsCap : Nat := 80
def xGroups := xKnown + 8 * knownMax
def idCap : Nat := 256
def xId := xGroups + groupSize * groupsCap
def randCap : Nat := 32
def xRand := xId + idCap
def nameCap : Nat := 1024
def xName := xRand + randCap
def msgCap : Nat := 256
def xMsg := xName + nameCap
def xTok := xMsg + msgCap
def xElem := xTok + 8
def xComp := xElem + 64
def xDec := xComp + 8
def xOut := xDec + 24
def xFirst := xOut + outMax

section
variable (es : List String)

def E : Nat := es.length
def xFlags : Nat := xFirst + 8 * (E es + 1)
def xRuleT : Nat := xFlags es + 8 * (E es + 1)
def xNameT : Nat := xRuleT es + 8 * (E es + 1)
def xNameBytes : Nat := xNameT es + 16 * E es
def nameBytes : Nat := (es.map String.length).sum
def size : Nat := xNameBytes es + (nameBytes es + 7) / 8 * 8

end

/-! ## Statements -/

def ofs : Nat := AbnfProg.areaOffset
def area : PStmt := areaAt ofs
def wd (o : Nat) : PExpr := word (v "a") o
def setW (o : Nat) (e : PExpr) : PStmt := .store (atOff (v "a") o) e
def neg1 : PExpr := n (2 ^ 64 - 1)
def inByte (i : String) : PExpr := byte (eAdd (atOff (v "a") aInput) (v i))
/-- The input's byte at the local `i`, `i` checked, into the new local `b`. -/
def readIn (b i : String) : List PStmt := [kept i (artMax - 1), .dec b (inByte i)]
def isWS (b : PExpr) : PExpr := eOr (eEq b (n 32)) (eEq b (n 9))
/-- White space or a line's end: what a list's names and a date's words are read without. -/
def isGap (b : PExpr) : PExpr := eOr (isWS b) (eOr (eEq b (n 13)) (eEq b (n 10)))
def isDig (b : PExpr) : PExpr := eAnd (eLe (n 48) b) (eLe b (n 57))
def lowerE (b : PExpr) : PExpr := eAdd b (eMul (n 32) (eAnd (eLe (n 65) b) (eLe b (n 90))))
def ftext (b : PExpr) : PExpr :=
  eOr (eAnd (eLe (n 33) b) (eLe b (n 57))) (eAnd (eLe (n 59) b) (eLe b (n 126)))
def ifs (c : PExpr) (t : List PStmt) : PStmt := .ite c t []

/-- Whether the bytes at area offset `o` spell `s`, in lower case, letters read without case. -/
def spells (o : Nat) (s : String) : PExpr :=
  (codes s).zipIdx.foldl (fun acc (c, i) => eAnd acc (eEq (lowerE (byte (atOff (v "a") (o + i)))) (n c)))
    (n 1)

/-- The bytes of `s` at the output's place `o`, which moves past them. -/
def putConst (s : String) : List PStmt :=
  [kept "o" (outMax - s.length)] ++
  (codes s).zipIdx.map (fun (c, i) => PStmt.storeb (eAdd (atOff (v "a") (xOut + i)) (v "o")) (n c)) ++
  [.assign "o" (eAdd (v "o") (n s.length))]

/-- The name of a refusal: `s` as the rules write it. -/
def constName (s : String) : List PStmt :=
  (codes s).zipIdx.map (fun (c, i) => PStmt.storeb (atOff (v "a") (xName + i)) (n c)) ++
  [setW xNameLen (n s.length)]

/-- The place of the word in `xTok`, counted from one, among `names`, or 0. -/
def tokIn (names : List String) : PExpr :=
  names.zipIdx.foldl (fun acc (s, k) =>
    eAdd acc (eMul (n (k + 1)) (eAnd (eEq (wd xTokLen) (n s.length)) (spells xTok (lowerS s))))) (n 0)

mutual
/-- A statement, a check of the flag of a failed check after it if it is a call. -/
def guardS : PStmt → List PStmt
  | .call r f as => [.call r f as, ifs (word (v "a") aBroken) [.ret (n 1)]]
  | .ite c t e => [.ite c (guardL t) (guardL e)]
  | .while c b => [.while c (guardL b)]
  | s => [s]
def guardL : List PStmt → List PStmt
  | [] => []
  | s :: rest => guardS s ++ guardL rest
end

/-! ## Functions -/

section
variable (r : Rules) (es : List String) (m : Mutant)

/-- Where the line from `q` ends: its CR, or `lim` if no CRLF ends one before it. -/
def artEol : PFun :=
  { name := "artEol", params := [(1, "q"), (1, "lim")], body :=
    [area, kept "lim" artMax, .dec "e" (v "q"), .dec "go" (n 1),
     .while (v "go")
       [.ite (eLt (eAdd (v "e") (n 1)) (v "lim"))
         [kept "e" (artMax - 2), .dec "c" (inByte "e"), .dec "f" (eAdd (v "e") (n 1)), .dec "d" (inByte "f"),
          .ite (eAnd (eEq (v "c") (n 13)) (if m == .crEndsLine then n 1 else eEq (v "d") (n 10)))
            [.assign "go" (n 0)] [inc "e"]]
         [.assign "e" (v "lim"), .assign "go" (n 0)]],
     .ret (v "e")] }

/-- The header section's shape: 0, its empty line's place in `xSep`, or the reason it fails, as
`checkWith` takes them in turn: no header, no empty line, too long, a line too long, malformed. -/
def artStruct : PFun :=
  { name := "artStruct", body :=
    [area, .dec "len" (wd xLen), kept "len" artMax,
     ifs (eEq (v "len") (n 0)) [.ret (n 1)],
     .call "e0" "artEol" [n 0, v "len"],
     ifs (eEq (v "e0") (n 0)) [.ret (n 1)],
     .dec "s" (n 0), .dec "sep" neg1, .dec "long" (n 0), .dec "mal" (n 0), .dec "go" (n 1),
     .while (v "go")
       [.call "e" "artEol" [v "s", v "len"],
        .ite (eEq (v "e") (v "len")) [.assign "go" (n 0)]
          [.ite (eEq (v "e") (v "s")) [.assign "sep" (v "s"), .assign "go" (n 0)]
            ([ifs (eLt (n r.lineMax) (eSub (v "e") (v "s"))) [.assign "long" (n 1)]] ++
             readIn "b" "s" ++
             [.ite (isWS (v "b")) [ifs (eEq (v "s") (n 0)) [.assign "mal" (n 1)]]
               [.dec "j" (v "s"), .dec "g" (n 1),
                .while (v "g")
                  [.ite (eLt (v "j") (v "e"))
                    (readIn "c" "j" ++
                     [.ite (eEq (v "c") (n 58)) [.assign "g" (n 0)]
                       [.ite (ftext (v "c")) [inc "j"] [.assign "mal" (n 1), .assign "g" (n 0)]]])
                    [.assign "mal" (n 1), .assign "g" (n 0)]],
                ifs (eEq (v "j") (v "s")) [.assign "mal" (n 1)]],
              .assign "s" (eAdd (v "e") (n 2))])]],
     ifs (eLt (v "sep") (n 0)) [.ret (n 2)],
     ifs (eLt (n r.headerMax) (v "sep")) [.ret (n 3)],
     ifs (v "long") [.ret (n 4)],
     ifs (v "mal") [.ret (n 5)],
     setW xSep (v "sep"), .ret (n 0)] }

/-- The end of the field at `p`, past its last CRLF; its name's length in `xNl`, its first line's
end in `xE1`. -/
def artField : PFun :=
  { name := "artField", params := [(1, "p")], body :=
    [area, .dec "sep" (wd xSep), kept "sep" artMax, .dec "j" (v "p"), .dec "go" (n 1),
     .while (v "go") (readIn "b" "j" ++ [.ite (eEq (v "b") (n 58)) [.assign "go" (n 0)] [inc "j"]]),
     setW xNl (eSub (v "j") (v "p")),
     .call "e" "artEol" [v "j", v "sep"],
     setW xE1 (v "e"),
     .dec "q" (eAdd (v "e") (n 2)), .assign "go" (n 1),
     .while (v "go")
       [.ite (eLt (v "q") (v "sep"))
         (readIn "c" "q" ++
          [.ite (isWS (v "c")) [.call "f" "artEol" [v "q", v "sep"], .assign "q" (eAdd (v "f") (n 2))]
            [.assign "go" (n 0)]])
         [.assign "go" (n 0)]],
     .ret (v "q")] }

/-- 1 if every byte from `s` to `e` is white space. -/
def artAllWS : PFun :=
  { name := "artAllWS", params := [(1, "s"), (1, "e")], body :=
    [area, .dec "i" (v "s"),
     .while (eLt (v "i") (v "e")) (readIn "b" "i" ++ [.ite (isWS (v "b")) [inc "i"] [.ret (n 0)]]),
     .ret (n 1)] }

/-- 1 if a line of the body of the field at `p` is white space alone (RFC 5536 §2.2). -/
def artBlank : PFun :=
  { name := "artBlank", params := [(1, "p")], body :=
    [area, .call "fe" "artField" [v "p"], .dec "nl" (wd xNl), .dec "e1" (wd xE1),
     .call "x" "artAllWS" [eAdd (eAdd (v "p") (v "nl")) (n 1), v "e1"],
     ifs (v "x") [.ret (n 1)],
     .dec "q" (eAdd (v "e1") (n 2)),
     .while (eLt (v "q") (v "fe"))
       [.call "f" "artEol" [v "q", v "fe"], .call "y" "artAllWS" [v "q", v "f"],
        ifs (v "y") [.ret (n 1)], .assign "q" (eAdd (v "f") (n 2))],
     .ret (n 0)] }

/-- The entry of the name of `nl` octets at `p`, compared without case, or `E es`. -/
def artClass : PFun :=
  let lower (b : PExpr) : PExpr := if m == .caseful then b else lowerE b
  { name := "artClass", params := [(1, "p"), (1, "nl")], body :=
    [area, kept "nl" artMax, .dec "k" (n 0),
     .while (eLt (v "k") (n (E es)))
       [.dec "t" (eAdd (atOff (v "a") (xNameT es)) (eMul (v "k") (n 16))),
        .dec "off" (.loadw 1 (v "t")), kept "off" (nameBytes es),
        .dec "ln" (.loadw 1 (atOff (v "t") 8)), kept "ln" 64,
        ifs (eEq (v "ln") (v "nl"))
          [.dec "i" (n 0), .dec "ok" (n 1),
           .while (eLt (v "i") (v "ln"))
             ([.dec "pi" (eAdd (v "p") (v "i"))] ++ readIn "b" "pi" ++
              [.dec "oi" (eAdd (v "off") (v "i")), kept "oi" (nameBytes es),
               ifs (ne (lower (v "b")) (byte (eAdd (atOff (v "a") (xNameBytes es)) (v "oi")))) [.assign "ok" (n 0)],
               inc "i"]),
           ifs (v "ok") [.ret (v "k")]],
        inc "k"],
     .ret (n (E es))] }

/-- The rules a field, its parts or the context are matched by. -/
def usedRules : List Nat :=
  (AbnfRules.fieldRules.map (·.2) ++ [AbnfRules.optionalField] ++
    ["mailbox", "path-identity", "newsgroup-name"].map AbnfProg.ruleIndex).eraseDups

/-- 1 if rule `rule` matches all of the input from `s` to `e`. -/
def artGrammar : PFun :=
  { name := "artGrammar", params := [(1, "rule"), (1, "s"), (1, "e")], body :=
    [area, kept "s" inputMax, kept "e" inputMax, setW aLen (v "e"),
     .call "z" "setClear" [n 0], .call "z1" "setClear" [n 1], .call "u" "setAdd" [n 0, v "s"]] ++
    usedRules.map (fun i => ifs (eEq (v "rule") (n i)) [rootCall i]) ++
    [.call "h" "setHas" [n 1, v "e"], .ret (v "h")] }

/-- The message identifiers from `s` to `e`, read as `ArticleSpec.msgIds` reads them: 1 if one is
longer than the bound; the first one's place and length in `xMsgS` and `xMsgL`. -/
def artMsgIds : PFun :=
  { name := "artMsgIds", params := [(1, "s"), (1, "e")], body :=
    [area, setW xMsgS neg1, setW xMsgL (n 0),
     .dec "i" (v "s"), .dec "dep" (n 0), .dec "cur" (n 0), .dec "cs" (n 0), .dec "cl" (n 0),
     .dec "long" (n 0), .dec "found" (n 0),
     .while (eLt (v "i") (v "e"))
       (readIn "b" "i" ++
        [.ite (v "cur")
          [inc "cl",
           ifs (eEq (v "b") (n 62))
             [.assign "cur" (n 0), ifs (eLt (n r.idMax) (v "cl")) [.assign "long" (n 1)],
              ifs (eEq (v "found") (n 0)) [setW xMsgS (v "cs"), setW xMsgL (v "cl"), .assign "found" (n 1)]],
           inc "i"]
          [.ite (eEq (v "dep") (n 0))
            [.ite (eEq (v "b") (n 40)) [.assign "dep" (n 1)]
               [ifs (eEq (v "b") (n 60)) [.assign "cur" (n 1), .assign "cs" (v "i"), .assign "cl" (n 1)]],
             inc "i"]
            [.ite (eAnd (eEq (v "b") (n 92)) (n (if m == .escapeKept then 0 else 1)))
               [.assign "i" (eAdd (v "i") (n 2))]
               [.ite (eEq (v "b") (n 40)) [inc "dep"]
                  [ifs (eEq (v "b") (n 41)) [.assign "dep" (eSub (v "dep") (n 1))]],
                inc "i"]]]]),
     .ret (v "long")] }

/-- Where the date of the Received field's body from `s` to `e` starts: past the one `;` outside
quoted strings, domain literals and comments, or `e` (`ArticleSpec.receivedDate`). -/
def artReceived : PFun :=
  { name := "artReceived", params := [(1, "s"), (1, "e")], body :=
    [area, .dec "i" (v "s"), .dec "mode" (n 0), .dec "dep" (n 0),
     .while (eLt (v "i") (v "e"))
       (readIn "b" "i" ++
        [.ite (eAnd (or2 (eEq (v "mode") (n 1)) (eLt (n 0) (v "dep"))) (eEq (v "b") (n 92)))
          [.assign "i" (eAdd (v "i") (n 2))]
          [.ite (eLt (n 0) (v "dep"))
            [.ite (eEq (v "b") (n 40)) [inc "dep"] [ifs (eEq (v "b") (n 41)) [.assign "dep" (eSub (v "dep") (n 1))]],
             inc "i"]
            [.ite (eEq (v "mode") (n 1)) [ifs (eEq (v "b") (n 34)) [.assign "mode" (n 0)], inc "i"]
              [.ite (eEq (v "mode") (n 2)) [ifs (eEq (v "b") (n 93)) [.assign "mode" (n 0)], inc "i"]
                [.ite (eEq (v "b") (n 34)) [.assign "mode" (n 1), inc "i"]
                  [.ite (eEq (v "b") (n 91)) [.assign "mode" (n 2), inc "i"]
                    [.ite (eEq (v "b") (n 40)) [.assign "dep" (n 1), inc "i"]
                      [ifs (eEq (v "b") (n 59)) [.ret (eAdd (v "i") (n 1))], inc "i"]]]]]]]]),
     .ret (v "e")] }

/-- The end of the next word from `p` before `e`, words parted by white space and line ends: its
start in `xTokS`, its length in `xTokLen` (0 if none), its first eight bytes in `xTok`. -/
def artTok : PFun :=
  { name := "artTok", params := [(1, "p"), (1, "e")], body :=
    [area, .dec "i" (v "p"), .dec "go" (n 1),
     .while (v "go")
       [.ite (eLt (v "i") (v "e")) (readIn "b" "i" ++ [.ite (isGap (v "b")) [inc "i"] [.assign "go" (n 0)]])
         [.assign "go" (n 0)]],
     setW xTokS (v "i"), .dec "ln" (n 0), .assign "go" (n 1),
     .while (v "go")
       [.ite (eLt (v "i") (v "e"))
         (readIn "c" "i" ++
          [.ite (isGap (v "c")) [.assign "go" (n 0)]
            [ifs (eLt (v "ln") (n 8)) [.storeb (eAdd (atOff (v "a") xTok) (v "ln")) (v "c")],
             ifs (eLt (v "ln") (n artMax)) [inc "ln"], inc "i"]])
         [.assign "go" (n 0)]],
     setW xTokLen (v "ln"), .ret (v "i")] }

/-- The number the digits from `s` to `e` write, at most `yearBig`, or -1 if they are none or not
all digits; the number modulo 400 in `xNumMod`. -/
def artNum : PFun :=
  { name := "artNum", params := [(1, "s"), (1, "e")], body :=
    [area, ifs (eLe (v "e") (v "s")) [.ret neg1],
     .dec "i" (v "s"), .dec "val" (n 0), .dec "md" (n 0),
     .while (eLt (v "i") (v "e"))
       (readIn "b" "i" ++
        [.ite (isDig (v "b"))
          [.assign "val" (eAdd (eMul (v "val") (n 10)) (eSub (v "b") (n 48))),
           ifs (eLt (n yearBig) (v "val")) [.assign "val" (n yearBig)],
           .assign "md" (eAdd (eMul (v "md") (n 10)) (eSub (v "b") (n 48))),
           .while (eLe (n 400) (v "md")) [.assign "md" (eSub (v "md") (n 400))],
           inc "i"]
          [.ret neg1]]),
     setW xNumMod (v "md"), .ret (v "val")] }

/-- `x / d`, for `x` below 2^62 and `d` from 1 to 2^62, bit by bit from the powers of two, from
the highest bit of `x`. -/
def artDiv : PFun :=
  { name := "artDiv", params := [(1, "x"), (1, "d")], body :=
    [area,
     ifs (or2 (or2 (eLt (v "x") (n 0)) (eLt (n (2 ^ 62 - 1)) (v "x")))
          (or2 (eLt (v "d") (n 1)) (eLt (n (2 ^ 62)) (v "d"))))
       [.store (atOff (v "a") aBroken) (n 1), .ret (n 0)],
     .dec "q" (n 0), .dec "rm" (n 0), .dec "j" (n 61), .dec "go" (n 1),
     .while (v "go")
       [kept "j" 63,
        .ite (eLe (pow (v "j")) (v "x")) [.assign "go" (n 0)]
          [.assign "j" (eSub (v "j") (n 1)), ifs (eLt (v "j") (n 0)) [.assign "go" (n 0)]]],
     .while (eLe (n 0) (v "j"))
       [kept "j" 63, .dec "pw" (pow (v "j")),
        .assign "rm" (eAdd (eAdd (v "rm") (v "rm")) (ne (eAnd (v "x") (v "pw")) (n 0))),
        ifs (eLe (v "d") (v "rm")) [.assign "rm" (eSub (v "rm") (v "d")), .assign "q" (eAdd (v "q") (v "pw"))],
        .assign "j" (eSub (v "j") (n 1))],
     .ret (v "q")] }

/-- The days since 1970-01-01 of a day of the Gregorian calendar (`ArticleSpec.daysFromCivil`). -/
def artCivil : PFun :=
  { name := "artCivil", params := [(1, "y"), (1, "mo"), (1, "d")], body :=
    [area, .dec "y1" (v "y"), ifs (eLe (v "mo") (n 2)) [.assign "y1" (eSub (v "y") (n 1))],
     .call "era" "artDiv" [v "y1", n 400], .dec "yoe" (eSub (v "y1") (eMul (v "era") (n 400))),
     .dec "mp" (eAdd (v "mo") (n 9)), ifs (eLt (n 2) (v "mo")) [.assign "mp" (eSub (v "mo") (n 3))],
     .call "q5" "artDiv" [eAdd (eMul (n 153) (v "mp")) (n 2), n 5],
     .call "q4" "artDiv" [v "yoe", n 4], .call "qc" "artDiv" [v "yoe", n 100],
     .ret (eSub (eAdd (eAdd (eMul (v "era") (n 146097)) (eMul (v "yoe") (n 365)))
        (eSub (eAdd (v "q4") (eSub (eAdd (v "q5") (v "d")) (n 1))) (v "qc"))) (n 719468))] }

/-- The seconds since 1970 the date-time from `s` to `e` says, as `ArticleSpec.dateValue` reads
it: 1 and the seconds in `xValue`; 0 if it says none; 2 if its year is `yearBig` or later. -/
def artDate : PFun :=
  let finish : List PStmt :=
    [ifs (eEq (v "cd") (n 0)) [.assign "bad" (n 1)],
     .ite (eEq (v "np") (n 0)) [.assign "hh" (v "cv")]
       [.ite (eEq (v "np") (n 1)) [.assign "mi" (v "cv")] [ifs (eEq (v "np") (n 2)) [.assign "se" (v "cv")]]],
     inc "np", .assign "cv" (n 0), .assign "cd" (n 0)]
  let toks (name : String) (p q : PExpr) : List PStmt :=
    [.call name "artTok" [p, q], ifs (eEq (wd xTokLen) (n 0)) [.ret (n 0)]]
  { name := "artDate", params := [(1, "s"), (1, "e")], body :=
    [area, .dec "c" (v "s"), .dec "go" (n 1),
     .while (v "go")
       [.ite (eLt (v "c") (v "e")) (readIn "b" "c" ++ [.ite (eEq (v "b") (n 40)) [.assign "go" (n 0)] [inc "c"]])
         [.assign "go" (n 0)]],
     .dec "nc" (n 0), .dec "cp" (n 0), .dec "i" (v "s"),
     .while (eLt (v "i") (v "c"))
       (readIn "b2" "i" ++ [ifs (eEq (v "b2") (n 44)) [ifs (eEq (v "nc") (n 0)) [.assign "cp" (v "i")], inc "nc"],
         inc "i"]),
     ifs (eLt (n 1) (v "nc")) [.ret (n 0)],
     .dec "wk" (n 0), .dec "hw" (n 0), .dec "ts" (v "s"),
     ifs (eEq (v "nc") (n 1))
       (toks "t1" (v "s") (v "cp") ++
        [.assign "wk" (tokIn ArticleSpec.dayNames), .assign "hw" (n 1),
         .call "t2" "artTok" [v "t1", v "cp"], ifs (ne (wd xTokLen) (n 0)) [.ret (n 0)],
         .assign "ts" (eAdd (v "cp") (n 1))]),
     ] ++ toks "p1" (v "ts") (v "c") ++ [.dec "ds" (wd xTokS)] ++
     toks "p2" (v "p1") (v "c") ++ [.dec "mo" (tokIn ArticleSpec.monthNames)] ++
     toks "p3" (v "p2") (v "c") ++ [.dec "ys" (wd xTokS),
     .call "dy" "artNum" [v "ds", v "p1"], ifs (eLt (v "dy") (n 0)) [.ret (n 0)],
     ifs (eEq (v "mo") (n 0)) [.ret (n 0)],
     .call "yr" "artNum" [v "ys", v "p3"], ifs (eLt (v "yr") (n 0)) [.ret (n 0)],
     .dec "y4" (wd xNumMod),
     ifs (eAnd (n (if m == .yearShort then 1 else 0)) (eLe (n yearBig) (v "yr"))) [.assign "y4" (n 0)],
     -- The time and the zone: the rest of the words, run together.
     .dec "j" (v "p3"), .dec "ph" (n 0), .dec "np" (n 0), .dec "cv" (n 0), .dec "cd" (n 0),
     .dec "hh" (n 0), .dec "mi" (n 0), .dec "se" (n 0), .dec "bad" (n 0),
     .dec "zl" (n 0), .dec "z0" (n 0), .dec "zd" (n 1), .dec "zv" (n 0), .dec "zg" (n 1),
     .while (eLt (v "j") (v "c"))
       (readIn "b3" "j" ++
        [ifs (eEq (isGap (v "b3")) (n 0))
          [.ite (eAnd (eEq (v "ph") (n 0)) (or2 (isDig (v "b3")) (eEq (v "b3") (n 58))))
            [.ite (eEq (v "b3") (n 58)) finish
              [.assign "cv" (eAdd (eMul (v "cv") (n 10)) (eSub (v "b3") (n 48))),
               ifs (eLt (n 1000) (v "cv")) [.assign "cv" (n 1000)], inc "cd"]]
            ([ifs (eEq (v "ph") (n 0)) (finish ++ [.assign "ph" (n 1)]),
              ifs (eEq (v "zl") (n 0)) [.assign "z0" (v "b3")]] ++
             ["g", "m", "t"].zipIdx.map (fun (c, k) =>
               ifs (eEq (v "zl") (n k)) [ifs (ne (lowerE (v "b3")) (n c.toList.head!.toNat)) [.assign "zg" (n 0)]]) ++
             [ifs (eAnd (eLe (n 1) (v "zl")) (eLe (v "zl") (n 4)))
                [.ite (isDig (v "b3")) [.assign "zv" (eAdd (eMul (v "zv") (n 10)) (eSub (v "b3") (n 48)))]
                  [.assign "zd" (n 0)]],
              inc "zl"])],
         inc "j"]),
     ifs (eEq (v "ph") (n 0)) finish,
     ifs (or2 (v "bad") (or2 (eLt (v "np") (n 2)) (eLt (n 3) (v "np")))) [.ret (n 0)],
     .dec "off" (n 0),
     .ite (eAnd (eEq (v "zl") (n 3)) (v "zg")) []
       [ifs (or2 (ne (v "zl") (n 5)) (eEq (v "zd") (n 0))) [.ret (n 0)],
        .call "zh" "artDiv" [v "zv", n 100], .dec "zm" (eSub (v "zv") (eMul (v "zh") (n 100))),
        ifs (eLe (n 60) (v "zm")) [.ret (n 0)],
        .assign "off" (eAdd (eMul (v "zh") (n 3600)) (eMul (v "zm") (n 60))),
        .ite (eEq (v "z0") (n 43)) []
          [.ite (eEq (v "z0") (n 45)) [.assign "off" (eSub (n 0) (v "off"))] [.ret (n 0)]]],
     .dec "lp" (eAnd (eEq (eAnd (v "y4") (n 3)) (n 0))
        (eAnd (ne (v "y4") (n 100)) (eAnd (ne (v "y4") (n 200)) (ne (v "y4") (n 300))))),
     .dec "dm" (n 31),
     .ite (eEq (v "mo") (n 2)) [.assign "dm" (eAdd (n 28) (v "lp"))]
       [ifs (or2 (or2 (eEq (v "mo") (n 4)) (eEq (v "mo") (n 6))) (or2 (eEq (v "mo") (n 9)) (eEq (v "mo") (n 11))))
         [.assign "dm" (n 30)]],
     ifs (or2 (or2 (eLt (v "yr") (n 1900)) (or2 (eLt (v "dy") (n 1)) (eLt (v "dm") (v "dy"))))
          (or2 (eLt (n 23) (v "hh")) (or2 (eLt (n 59) (v "mi")) (eLt (n 60) (v "se")))))
       [.ret (n 0)],
     .dec "ye" (v "yr"), ifs (eLe (n yearBig) (v "yr")) [.assign "ye" (eAdd (n 2000) (v "y4"))],
     .call "days" "artCivil" [v "ye", v "mo", v "dy"]] ++
    (if m == .weekdayUnchecked then [] else
      [ifs (v "hw")
        [ifs (eEq (v "wk") (n 0)) [.ret (n 0)],
         .call "q7" "artDiv" [eAdd (v "days") (n 700004), n 7],
         ifs (ne (eSub (v "wk") (n 1)) (eSub (eAdd (v "days") (n 700004)) (eMul (v "q7") (n 7)))) [.ret (n 0)]]]) ++
    [ifs (eLe (n yearBig) (v "yr")) [.ret (n 2)],
     setW xValue (eSub (eAdd (eMul (v "days") (n 86400))
       (eAdd (eAdd (eMul (v "hh") (n 3600)) (eMul (v "mi") (n 60))) (v "se"))) (v "off")),
     .ret (n 1)] }

/-- The output's place past the decimal digits of `x`, a word read without sign, written at `o`. -/
def artNum10 : PFun :=
  { name := "artNum10", params := [(1, "o"), (1, "x")], body :=
    [area, .dec "k" (n 0), .dec "y" (v "x"), .dec "go" (n 1),
     .while (v "go")
       [.dec "hi" (.shr (v "y") (n 32)), .dec "lo" (eAnd (v "y") (n 4294967295)),
        .dec "qh" (.shr (eMul (v "hi") (n 3435973837)) (n 35)),
        .dec "rh" (eSub (v "hi") (eMul (v "qh") (n 10))),
        .dec "t" (eAdd (eMul (v "rh") (n 6)) (v "lo")),
        .dec "qt" (.shr (eMul (v "t") (n 3435973837)) (n 35)),
        .dec "q" (eAdd (eAdd (eMul (v "qh") (n 4294967296)) (eMul (v "rh") (n 429496729))) (v "qt")),
        kept "k" 23,
        .storeb (eAdd (atOff (v "a") xDec) (v "k")) (eAdd (n 48) (eSub (v "y") (eMul (v "q") (n 10)))),
        inc "k", .assign "y" (v "q"), ifs (eEq (v "y") (n 0)) [.assign "go" (n 0)]],
     .while (eLt (n 0) (v "k"))
       [.assign "k" (eSub (v "k") (n 1)), kept "k" 23, kept "o" (outMax - 1),
        .storeb (eAdd (atOff (v "a") xOut) (v "o")) (byte (eAdd (atOff (v "a") xDec) (v "k"))), inc "o"],
     .ret (v "o")] }

/-- The output's place past `len` bytes of the area copied from `from` to `o`. -/
def artCopy : PFun :=
  { name := "artCopy", params := [(1, "o"), (1, "src"), (1, "len")], body :=
    [area, .dec "i" (n 0),
     .while (eLt (v "i") (v "len"))
       ([.dec "f" (eAdd (v "src") (v "i"))] ++ (if m == .unkept then [] else [kept "f" (size es - 1)]) ++
        [kept "o" (outMax - 1),
         .storeb (eAdd (atOff (v "a") xOut) (v "o")) (byte (eAdd (v "a") (v "f"))), inc "i", inc "o"]),
     .ret (v "o")] }

/-- The `len` bytes of the area from `from` as the message identifier. -/
def artToMsg : PFun :=
  { name := "artToMsg", params := [(1, "src"), (1, "len")], body :=
    [area, kept "len" (msgCap - 1), .dec "i" (n 0),
     .while (eLt (v "i") (v "len"))
       [.dec "f" (eAdd (v "src") (v "i")), kept "f" (size es - 1),
        .storeb (eAdd (atOff (v "a") xMsg) (v "i")) (byte (eAdd (v "a") (v "f"))), inc "i"],
     setW xMsgLen (v "len"), .ret (n 0)] }

/-- The name of the field at `p` as the name of a refusal. -/
def artNameAt : PFun :=
  { name := "artNameAt", params := [(1, "p")], body :=
    [area, .call "fe" "artField" [v "p"], .dec "nl" (wd xNl), kept "nl" (nameCap - 1), .dec "i" (n 0),
     .while (eLt (v "i") (v "nl"))
       ([.dec "f" (eAdd (v "p") (v "i"))] ++ readIn "b" "f" ++
        [.storeb (eAdd (atOff (v "a") xName) (v "i")) (v "b"), inc "i"]),
     setW xNameLen (v "nl"), .ret (n 0)] }

/-- The next name of a list from `p` before `e`, separated by `sep`, white space and line ends
read without: its first 64 bytes in `xElem`, its length, at most 65, in `xElemLen`, whether it is
a reserved group (`ArticleSpec.reserved`) in `xElemRes`; the place past it and its separator. -/
def artElem : PFun :=
  let comp (s : String) : PExpr := eAnd (eEq (v "cl") (n s.length))
    ((codes s).zipIdx.foldl (fun acc (c, i) => eAnd acc (eEq (byte (atOff (v "a") (xComp + i))) (n c))) (n 1))
  let whole (s : String) : PExpr := eAnd (eEq (v "ln") (n s.length))
    ((codes s).zipIdx.foldl (fun acc (c, i) => eAnd acc (eEq (byte (atOff (v "a") (xElem + i))) (n c))) (n 1))
  let done : List PStmt :=
    [ifs (or2 (or2 (comp "all") (comp "ctl"))
        (eAnd (v "first") (or2 (comp "example") (or2 (comp "to") (comp "control"))))) [.assign "res" (n 1)],
     .assign "first" (n 0), .assign "cl" (n 0)]
  { name := "artElem", params := [(1, "p"), (1, "e"), (1, "sep")], body :=
    [area, .dec "i" (v "p"), .dec "ln" (n 0), .dec "cl" (n 0), .dec "first" (n 1), .dec "res" (n 0),
     .dec "go" (n 1),
     .while (v "go")
       [.ite (eLt (v "i") (v "e"))
         (readIn "b" "i" ++
          [.ite (eEq (v "b") (v "sep")) [.assign "go" (n 0), inc "i"]
            [.ite (isGap (v "b")) [inc "i"]
              [ifs (eLt (v "ln") (n 64)) [.storeb (eAdd (atOff (v "a") xElem) (v "ln")) (v "b")],
               ifs (eLt (v "ln") (n 65)) [inc "ln"],
               .ite (eEq (v "b") (n 46)) done
                 [ifs (eLt (v "cl") (n 8)) [.storeb (eAdd (atOff (v "a") xComp) (v "cl")) (v "b")],
                  ifs (eLt (v "cl") (n 9)) [inc "cl"]],
               inc "i"]]])
         [.assign "go" (n 0)]]] ++ done ++
    [ifs (or2 (whole "poster") (whole "junk")) [.assign "res" (n 1)],
     setW xElemLen (v "ln"), setW xElemRes (v "res"), .ret (v "i")] }

/-- The place among the context's groups of the name in `xElem`, of `ln` octets, or -1. -/
def artKnown : PFun :=
  { name := "artKnown", params := [(1, "ln")], body :=
    [area, kept "ln" 64, .dec "gn" (wd xGroupsN), kept "gn" 64, .dec "j" (n 0),
     .while (eLt (v "j") (v "gn"))
       [.dec "t" (eAdd (atOff (v "a") xGroups) (eMul (v "j") (n groupSize))),
        ifs (eEq (.loadw 1 (v "t")) (v "ln"))
          [.dec "i" (n 0), .dec "ok" (n 1),
           .while (eLt (v "i") (v "ln"))
             [kept "i" 63,
              ifs (ne (byte (eAdd (atOff (v "a") xElem) (v "i"))) (byte (eAdd (atOff (v "t") 8) (v "i"))))
                [.assign "ok" (n 0)],
              inc "i"],
           ifs (v "ok") [.ret (v "j")]],
        inc "j"],
     .ret neg1] }

/-- Newsgroups' body from `s` to `e`: how many groups it names in `xGCount`, whether one is reserved
in `xGRes`, whether the server carries one in `xGKnown`, those it carries, each once, in `xKnown`. -/
def artGroups : PFun :=
  { name := "artGroups", params := [(1, "s"), (1, "e")], body :=
    [area, setW xKnownN (n 0), .dec "cnt" (n 0), .dec "rs" (n 0), .dec "kn" (n 0), .dec "p" (v "s"),
     .while (eLt (v "p") (v "e"))
       [.call "q" "artElem" [v "p", v "e", n 44], .dec "ln" (wd xElemLen),
        ifs (eLt (n 0) (v "ln"))
          [inc "cnt", ifs (wd xElemRes) [.assign "rs" (n 1)],
           ifs (eLe (v "ln") (n 64))
             [.call "j" "artKnown" [v "ln"],
              ifs (eLe (n 0) (v "j"))
                [.assign "kn" (n 1), .dec "kc" (wd xKnownN), kept "kc" knownMax, .dec "x" (n 0), .dec "dup" (n 0),
                 .while (eLt (v "x") (v "kc"))
                   [kept "x" (knownMax - 1),
                    ifs (eEq (.loadw 1 (eAdd (atOff (v "a") xKnown) (eMul (v "x") (n 8)))) (v "j")) [.assign "dup" (n 1)],
                    inc "x"],
                 ifs (eAnd (eEq (v "dup") (n 0)) (eLt (v "kc") (n knownMax)))
                   [.store (eAdd (atOff (v "a") xKnown) (eMul (v "kc") (n 8))) (v "j"),
                    setW xKnownN (eAdd (v "kc") (n 1))]]]],
        .assign "p" (v "q")],
     setW xGCount (v "cnt"), setW xGRes (v "rs"), setW xGKnown (v "kn"), .ret (n 0)] }

/-- 1 if Distribution's body from `s` to `e` names "all" (RFC 5536 §3.2.4). -/
def artDistAll : PFun :=
  { name := "artDistAll", params := [(1, "s"), (1, "e")], body :=
    [area, .dec "p" (v "s"),
     .while (eLt (v "p") (v "e"))
       [.call "q" "artElem" [v "p", v "e", n 44],
        ifs (eAnd (eEq (wd xElemLen) (n 3)) (spells xElem "all")) [.ret (n 1)],
        .assign "p" (v "q")],
     .ret (n 0)] }

/-- 1 if Path's body from `s` to `e` holds the diagnostic POSTED (`ArticleSpec.isPosted`). -/
def artPosted : PFun :=
  { name := "artPosted", params := [(1, "s"), (1, "e")], body :=
    [area, .dec "p" (v "s"),
     .while (eLt (v "p") (v "e"))
       [.call "q" "artElem" [v "p", v "e", n 33], .dec "ln" (wd xElemLen),
        ifs (eAnd (eAnd (eLt (n 6) (v "ln")) (eEq (byte (atOff (v "a") xElem)) (n 46)))
            (eAnd (spells (xElem + 1) "posted") (or2 (eEq (v "ln") (n 7)) (eEq (byte (atOff (v "a") (xElem + 7))) (n 46)))))
          [.ret (n 1)],
        .assign "p" (v "q")],
     .ret (n 0)] }

/-- The output's place past the two digits of `x`, below 100, written at `o`. -/
def pad2 (x : PExpr) (k : Nat) : List PStmt :=
  [.call s!"t{k}" "artDiv" [x, n 10], kept "o" (outMax - 2),
   .storeb (eAdd (atOff (v "a") xOut) (v "o")) (eAdd (n 48) (v s!"t{k}")),
   .storeb (eAdd (atOff (v "a") (xOut + 1)) (v "o")) (eAdd (n 48) (eSub x (eMul (v s!"t{k}") (n 10)))),
   .assign "o" (eAdd (v "o") (n 2))]

/-- The output's place past the date of the wall clock, written at `o` as the server writes one
(`ArticleSpec.formatDate`). -/
def artFormat : PFun :=
  { name := "artFormat", params := [(1, "o")], body :=
    [area, .dec "wl" (wd xWall),
     .call "dd" "artDiv" [v "wl", n 86400], .dec "sc" (eSub (v "wl") (eMul (v "dd") (n 86400))),
     .dec "z" (eAdd (v "dd") (n 719468)), .call "era" "artDiv" [v "z", n 146097],
     .dec "doe" (eSub (v "z") (eMul (v "era") (n 146097))),
     .call "a1" "artDiv" [v "doe", n 1460], .call "a2" "artDiv" [v "doe", n 36524],
     .call "a3" "artDiv" [v "doe", n 146096],
     .call "yoe" "artDiv" [eSub (eAdd (eSub (v "doe") (v "a1")) (v "a2")) (v "a3"), n 365],
     .call "b1" "artDiv" [v "yoe", n 4], .call "b2" "artDiv" [v "yoe", n 100],
     .dec "doy" (eSub (v "doe") (eSub (eAdd (eMul (n 365) (v "yoe")) (v "b1")) (v "b2"))),
     .call "mp" "artDiv" [eAdd (eMul (n 5) (v "doy")) (n 2), n 153],
     .call "c1" "artDiv" [eAdd (eMul (n 153) (v "mp")) (n 2), n 5],
     .dec "dy" (eAdd (eSub (v "doy") (v "c1")) (n 1)),
     .dec "mo" (eAdd (v "mp") (n 3)), ifs (eLe (n 10) (v "mp")) [.assign "mo" (eSub (v "mp") (n 9))],
     .dec "yr" (eAdd (v "yoe") (eMul (v "era") (n 400))), ifs (eLe (v "mo") (n 2)) [inc "yr"],
     .call "q7" "artDiv" [eAdd (v "dd") (n 4), n 7],
     .dec "wk" (eSub (eAdd (v "dd") (n 4)) (eMul (v "q7") (n 7))),
     .call "hr" "artDiv" [v "sc", n 3600], .dec "rest" (eSub (v "sc") (eMul (v "hr") (n 3600))),
     .call "mn" "artDiv" [v "rest", n 60]] ++
    ArticleSpec.dayNames.zipIdx.map (fun (s, k) => ifs (eEq (v "wk") (n k)) (putConst s)) ++
    putConst ", " ++ pad2 (v "dy") 0 ++ putConst " " ++
    ArticleSpec.monthNames.zipIdx.map (fun (s, k) => ifs (eEq (v "mo") (n (k + 1))) (putConst s)) ++
    putConst " " ++ [.call "o1" "artNum10" [v "o", v "yr"], .assign "o" (v "o1")] ++ putConst " " ++
    pad2 (v "hr") 1 ++ putConst ":" ++ pad2 (v "mn") 2 ++ putConst ":" ++
    pad2 (eSub (v "rest") (eMul (v "mn") (n 60))) 3 ++ putConst " +0000" ++ [.ret (v "o")] }

/-- Where the first field of the name lies, -1 if none does. -/
def firstOf (s : String) : PExpr := wd (xFirst + 8 * entryOf es s)

/-- The header section stored: Path first, the fields kept, Message-ID and Date if made,
Injection-Info, Injection-Date if added (`ArticleSpec.added`); its message identifier. -/
def artAdded : PFun :=
  let k := entryOf es
  let combos := [false, true].flatMap fun i => [false, true].flatMap fun mi => [false, true].map (i, mi, ·)
  let flag (s : String) : PExpr := eLe (n 0) (firstOf es s)
  let addDate : PExpr := combos.foldl (fun acc (i, mi, d) =>
    if r.injectionDate i mi d then
      eOr acc (eAnd (eEq (flag "Injection-Date") (n i.toNat))
        (eAnd (eEq (flag "Message-ID") (n mi.toNat)) (eEq (flag "Date") (n d.toNat))))
    else acc) (n 0)
  let copy (name : String) (src len : PExpr) : List PStmt :=
    [.call name "artCopy" [v "o", src, len], .assign "o" (v name)]
  let fmt (name : String) : List PStmt := [.call name "artFormat" [v "o"], .assign "o" (v name)]
  let num (name : String) (x : PExpr) : List PStmt := [.call name "artNum10" [v "o", x], .assign "o" (v name)]
  { name := "artAdded", body :=
    [area, .dec "o" (n 0), .dec "idl" (wd xIdLen), kept "idl" 200, .dec "rl" (wd xRandLen), kept "rl" 16] ++
    putConst "Path: " ++ copy "o1" (n xId) (v "idl") ++ putConst "!.POSTED" ++
    [.dec "pp" (firstOf es "Path"),
     .ite (eLe (n 0) (v "pp"))
       ([.call "pf" "artField" [v "pp"], .dec "pn" (wd xNl), .dec "pe" (wd xE1),
         .dec "r0" (eAdd (eAdd (v "pp") (v "pn")) (n 1)), .dec "g" (n 1),
         .while (v "g")
           [.ite (eLt (v "r0") (v "pe")) (readIn "c" "r0" ++ [.ite (isWS (v "c")) [inc "r0"] [.assign "g" (n 0)]])
             [.assign "g" (n 0)]],
         .ite ((if m == .foldEarly then eLe else eLt) (n r.lineMax)
             (eAdd (n 15) (eAdd (v "idl") (eSub (v "pe") (v "r0")))))
           (putConst "\r\n !") (putConst "!")] ++
        copy "o2" (eAdd (n aInput) (v "r0")) (eSub (v "pe") (v "r0")) ++ putConst "\r\n" ++
        copy "o3" (eAdd (n (aInput + 2)) (v "pe")) (eSub (v "pf") (eAdd (v "pe") (n 2))))
       (putConst "!not-for-mail\r\n"),
     .dec "sep" (wd xSep), .dec "p" (n 0),
     .while (eLt (v "p") (v "sep"))
       [.call "fe" "artField" [v "p"], .call "ck" "artClass" [v "p", wd xNl],
        ifs (eAnd (ne (v "ck") (n (k "Path")))
            (if r.replace then eAnd (ne (v "ck") (n (k "Message-ID"))) (ne (v "ck") (n (k "Date"))) else n 1))
          (copy "o4" (eAdd (n aInput) (v "p")) (eSub (v "fe") (v "p"))),
        .assign "p" (v "fe")],
     .dec "hid" (firstOf es "Message-ID"),
     .ite (if r.replace then n 1 else eLt (v "hid") (n 0))
       (putConst "Message-ID: " ++ [.dec "ms" (v "o")] ++ putConst "<" ++ num "o5" (wd xSeq) ++ putConst "." ++
        copy "o6" (n xRand) (v "rl") ++ putConst "@" ++ copy "o7" (n xId) (v "idl") ++ putConst ">" ++
        [.call "tm" "artToMsg" [eAdd (n xOut) (v "ms"), eSub (v "o") (v "ms")]] ++ putConst "\r\n")
       [.call "hf" "artField" [v "hid"], .dec "hn" (wd xNl),
        .call "ml" "artMsgIds" [eAdd (eAdd (v "hid") (v "hn")) (n 1), eSub (v "hf") (n 2)],
        setW xMsgLen (n 0),
        ifs (eLe (n 0) (wd xMsgS)) [.call "tn" "artToMsg" [eAdd (n aInput) (wd xMsgS), wd xMsgL]]],
     ifs (if r.replace then n 1 else eLt (firstOf es "Date") (n 0))
       (putConst "Date: " ++ fmt "o8" ++ putConst "\r\n")] ++
    putConst "Injection-Info: " ++ copy "o9" (n xId) (v "idl") ++ putConst "; logging-data=" ++
    num "oa" (wd xRun) ++ putConst "." ++ num "ob" (wd xConn) ++ putConst "\r\n" ++
    [ifs addDate (putConst "Injection-Date: " ++ fmt "oc" ++ putConst "\r\n"),
     setW xOutLen (v "o"), .ret (n 0)] }

/-- **What a POST makes of the proto-article**: 0, accepted, its header section, message identifier
and groups made; or the refusal's number, counted from 1 in the order of `Refusal`, its name. -/
def artCheck : PFun :=
  let field (pre : String) (at_ : PExpr) : List PStmt :=
    [.dec s!"{pre}p" at_, .call s!"{pre}f" "artField" [v s!"{pre}p"], .dec s!"{pre}n" (wd xNl),
     .dec s!"{pre}s" (eAdd (eAdd (v s!"{pre}p") (v s!"{pre}n")) (n 1)), .dec s!"{pre}e" (eSub (v s!"{pre}f") (n 2))]
  let window (pre nm : String) : PStmt :=
    ifs (eLe (n 0) (firstOf es nm))
      (field pre (firstOf es nm) ++
       [.call s!"{pre}v" "artDate" [v s!"{pre}s", v s!"{pre}e"],
        ifs (eEq (v s!"{pre}v") (n 2)) (constName nm ++ [.ret (n 19)]),
        ifs (eEq (v s!"{pre}v") (n 1))
          [.dec s!"{pre}t" (wd xValue),
           ifs (eLt (n r.ahead) (eSub (v s!"{pre}t") (wd xWall))) (constName nm ++ [.ret (n 19)]),
           ifs (eLt (n r.past) (eSub (wd xWall) (v s!"{pre}t"))) (constName nm ++ [.ret (n 20)])]])
  let bit (b : Nat) : PExpr := ne (eAnd (v "fl") (n b)) (n 0)
  { name := "artCheck", body :=
    [area, setW xNameLen (n 0), setW xOutLen (n 0), setW xMsgLen (n 0), setW xKnownN (n 0),
     .call "sh" "artStruct" [], ifs (v "sh") [.ret (v "sh")],
     .dec "sep" (wd xSep), kept "sep" artMax,
     .dec "i" (n 0),
     .while (eLt (v "i") (n (E es + 1)))
       [.store (eAdd (atOff (v "a") xFirst) (eMul (v "i") (n 8))) neg1, inc "i"],
     .dec "rep" neg1, .dec "lid" neg1, .dec "bd" neg1, .dec "p" (n 0),
     .while (eLt (v "p") (v "sep"))
       ([.call "fe" "artField" [v "p"], .dec "nl" (wd xNl),
         .call "k" "artClass" [v "p", v "nl"], kept "k" (E es),
         .dec "fl" (.loadw 1 (eAdd (atOff (v "a") (xFlags es)) (eMul (v "k") (n 8)))),
         .dec "ru" (.loadw 1 (eAdd (atOff (v "a") (xRuleT es)) (eMul (v "k") (n 8)))),
         .dec "why" (n 0),
         .ite (bit 1) [.assign "why" (n 6)]
           [.ite (bit 2) [.assign "why" (n 7)]
             [.ite (bit 4) [.assign "why" (n 8)] [ifs (bit 8) [.assign "why" (n 9)]]]]] ++
        (if r.blank then
          [ifs (eEq (v "why") (n 0)) [.call "bl" "artBlank" [v "p"], ifs (v "bl") [.assign "why" (n 10)]]]
         else []) ++
        [ifs (eEq (v "why") (n 0))
           [.call "g" "artGrammar" [v "ru", v "p", v "fe"], ifs (eEq (v "g") (n 0)) [.assign "why" (n 11)]],
         ifs (v "why") [.call "cn" "artNameAt" [v "p"], .ret (v "why")],
         .dec "fk" (.loadw 1 (eAdd (atOff (v "a") xFirst) (eMul (v "k") (n 8)))),
         .ite (eLt (v "fk") (n 0)) [.store (eAdd (atOff (v "a") xFirst) (eMul (v "k") (n 8))) (v "p")]
           [ifs (eAnd (bit 16) (eLt (v "rep") (n 0))) [.assign "rep" (v "p")]],
         .dec "vs" (eAdd (eAdd (v "p") (v "nl")) (n 1)), .dec "ve" (eSub (v "fe") (n 2)),
         ifs (eAnd (bit 32) (eLt (v "lid") (n 0)))
           [.call "ml" "artMsgIds" [v "vs", v "ve"], ifs (v "ml") [.assign "lid" (v "p")]]] ++
        (if r.dates then
          [ifs (eAnd (or2 (bit 64) (bit 128)) (eLt (v "bd") (n 0)))
            [.dec "ds" (v "vs"),
             ifs (bit 128) [.call "rd" "artReceived" [v "vs", v "ve"], .assign "ds" (v "rd")],
             .call "dv" "artDate" [v "ds", v "ve"], ifs (eEq (v "dv") (n 0)) [.assign "bd" (v "p")]]]
         else []) ++
        [.assign "p" (v "fe")]),
     ifs (eLe (n 0) (v "rep")) [.call "cr" "artNameAt" [v "rep"], .ret (n 12)]] ++
    r.required.map (fun nm => ifs (eLt (firstOf es nm) (n 0)) (constName nm ++ [.ret (n 13)])) ++
    (if r.posted then
      [ifs (eLe (n 0) (firstOf es "Path"))
        (field "h" (firstOf es "Path") ++ [.call "po" "artPosted" [v "hs", v "he"], ifs (v "po") [.ret (n 14)]])]
     else []) ++
    [ifs (eLe (n 0) (v "lid")) [.call "cl" "artNameAt" [v "lid"], .ret (n 15)]] ++
    (if r.sender then
      [ifs (eAnd (eLt (firstOf es "Sender") (n 0)) (eLe (n 0) (firstOf es "From")))
        (field "f" (firstOf es "From") ++
         [.call "mb" "artGrammar" [n (AbnfProg.ruleIndex "mailbox"), v "fs", v "fe"],
          ifs (eEq (v "mb") (n 0)) [.ret (n 16)]])]
     else []) ++
    (if r.distributionAll then
      [ifs (eLe (n 0) (firstOf es "Distribution"))
        (field "d" (firstOf es "Distribution") ++ [.call "da" "artDistAll" [v "ds", v "de"], ifs (v "da") [.ret (n 17)]])]
     else []) ++
    [ifs (eLe (n 0) (v "bd")) [.call "cb" "artNameAt" [v "bd"], .ret (n 18)],
     window "w" "Date", window "x" "Injection-Date",
     setW xGCount (n 0), setW xGRes (n 0), setW xGKnown (n 0),
     ifs (eLe (n 0) (firstOf es "Newsgroups"))
       (field "n" (firstOf es "Newsgroups") ++ [.call "gr" "artGroups" [v "ns", v "ne"]]),
     ifs (eLt (n r.groupsMax) (wd xGCount)) [.ret (n 21)]] ++
    (if r.reserved then [ifs (wd xGRes) [.ret (n 22)]] else []) ++
    (if r.known then [ifs (eEq (wd xGKnown) (n 0)) [.ret (n 23)]] else []) ++
    [.call "ad" "artAdded" [], .ret (n 0)] }

/-- 1 if the context fits what the server adds (`ArticleSpec.Context.ok`). -/
def artContext : PFun :=
  let toInput (len : String) (src : PExpr) : List PStmt :=
    [.dec s!"{len}i" (n 0),
     .while (eLt (v s!"{len}i") (v len))
       [kept s!"{len}i" (idCap - 1),
        .storeb (eAdd (atOff (v "a") aInput) (v s!"{len}i")) (byte (eAdd src (v s!"{len}i"))), inc s!"{len}i"]]
  { name := "artContext", body :=
    [area, .dec "il" (wd xIdLen), ifs (or2 (eLt (v "il") (n 0)) (eLt (n 200) (v "il"))) [.ret (n 0)]] ++
    toInput "il" (atOff (v "a") xId) ++
    [.call "gi" "artGrammar" [n (AbnfProg.ruleIndex "path-identity"), n 0, v "il"],
     ifs (eEq (v "gi") (n 0)) [.ret (n 0)],
     .dec "rl" (wd xRandLen), ifs (or2 (eLt (v "rl") (n 1)) (eLt (n 16) (v "rl"))) [.ret (n 0)],
     .dec "j" (n 0),
     .while (eLt (v "j") (v "rl"))
       [kept "j" (randCap - 1), .dec "b" (byte (eAdd (atOff (v "a") xRand) (v "j"))),
        .ite (or2 (isDig (v "b")) (eAnd (eLe (n 97) (v "b")) (eLe (v "b") (n 102)))) [inc "j"] [.ret (n 0)]],
     .dec "gn" (wd xGroupsN), ifs (or2 (eLt (v "gn") (n 0)) (eLt (n 64) (v "gn"))) [.ret (n 0)],
     .dec "x" (n 0),
     .while (eLt (v "x") (v "gn"))
       ([.dec "t" (eAdd (atOff (v "a") xGroups) (eMul (v "x") (n groupSize))), .dec "gl" (.loadw 1 (v "t")),
         ifs (or2 (eLt (v "gl") (n 0)) (eLt (n 64) (v "gl"))) [.ret (n 0)]] ++
        toInput "gl" (atOff (v "t") 8) ++
        [.call "ge" "artElem" [n 0, v "gl", n 44], ifs (wd xElemRes) [.ret (n 0)],
         .call "gg" "artGrammar" [n (AbnfProg.ruleIndex "newsgroup-name"), n 0, v "gl"],
         ifs (eEq (v "gg") (n 0)) [.ret (n 0)],
         .dec "y" (n 0),
         .while (eLt (v "y") (v "x"))
           [.dec "u" (eAdd (atOff (v "a") xGroups) (eMul (v "y") (n groupSize))),
            ifs (eEq (.loadw 1 (v "u")) (v "gl"))
              [.dec "i" (n 0), .dec "same" (n 1),
               .while (eLt (v "i") (v "gl"))
                 [kept "i" 63,
                  ifs (ne (byte (eAdd (atOff (v "t") 8) (v "i"))) (byte (eAdd (atOff (v "u") 8) (v "i"))))
                    [.assign "same" (n 0)],
                  inc "i"],
               ifs (v "same") [.ret (n 0)]],
            inc "y"],
         inc "x"]),
     .ret (n 1)] }

/-- The entries' tables: each name's place and length among their bytes, in lower case, what it is
to the rules and the rule its field is matched by. -/
def artTables : PFun :=
  let offs := (es.map String.length).foldl (fun acc l => acc ++ [acc.getLast?.getD 0 + l]) [0]
  { name := "artTables", body :=
    [area] ++
    (es.zip offs).zipIdx.flatMap (fun ((s, o), k) =>
      [setW (xNameT es + 16 * k) (n o), setW (xNameT es + 16 * k + 8) (n s.length),
       setW (xFlags es + 8 * k) (n (flagsOf r s)), setW (xRuleT es + 8 * k) (n (ruleOfName s))] ++
      (codes (lowerS s)).zipIdx.map fun (c, i) => PStmt.storeb (atOff (v "a") (xNameBytes es + o + i)) (n c)) ++
    [setW (xFlags es + 8 * E es) (n 0), setW (xRuleT es + 8 * E es) (n AbnfRules.optionalField), .ret (n 0)] }

/-- The functions, each after those it calls; the article's return after a call if a check failed
below it, so that no loop goes on with what the failed check returned. -/
def functions : List PFun :=
  AbnfProg.functions .none ofs ++ List.map (fun f => { f with body := guardL f.body })
  [artEol m, artStruct r, artField, artAllWS, artBlank, artClass es m, artGrammar, artMsgIds r m,
   artReceived, artTok, artNum, artDiv, artCivil, artDate m, artNum10, artCopy es m, artToMsg es,
   artNameAt, artElem, artKnown, artGroups, artDistAll, artPosted, artFormat, artAdded r es m,
   artCheck r es, artContext, artTables r es]

/-- A program that answers each request its host hands it: 3, the context, 1 if it fits; 0, the
article's verdict; 1, the date of the wall clock; 2, the seconds a date says, 0 if it says some
and 1 if none. It answers 255 to a request out of range or on a failed check. -/
def main : PFun :=
  { name := "main", body :=
    [area, .call "t" "tables" [], .call "u" "artTables" [], setW xCtxOk (n 0),
     .while (n 1)
       [.ffi "dn_next" [v "a", n 8, v "a", n (size es)],
        .store (atOff (v "a") aBroken) (n 0),
        .dec "md" (wd xMode), .dec "ans" (n 255), .dec "wl" (wd xWall), .dec "ln" (wd xLen),
        .dec "inw" (eAnd (eLe (n 0) (v "wl")) (eLt (v "wl") (n wallMax))),
        .dec "inl" (eAnd (eLe (n 0) (v "ln")) (eLe (v "ln") (n artMax))),
        ifs (eEq (v "md") (n 3)) [.call "c" "artContext" [], setW xCtxOk (v "c"), .assign "ans" (v "c")],
        ifs (eAnd (eEq (v "md") (n 0)) (eAnd (eEq (wd xCtxOk) (n 1)) (eAnd (v "inw") (v "inl"))))
          [.call "vd" "artCheck" [], .assign "ans" (v "vd")],
        ifs (eAnd (eEq (v "md") (n 1)) (v "inw"))
          [.call "f" "artFormat" [n 0], setW xOutLen (v "f"), .assign "ans" (n 0)],
        ifs (eAnd (eEq (v "md") (n 2)) (v "inl"))
          [.call "d" "artDate" [n 0, v "ln"],
           .ite (eEq (v "d") (n 1)) [.assign "ans" (n 0)] [ifs (eEq (v "d") (n 0)) [.assign "ans" (n 1)]]],
        ifs (word (v "a") aBroken) [.assign "ans" (n 255)],
        setW xVerdict (v "ans")],
     .ret (n 0)] }

end

/-- The heap the program needs: the header, then the area. -/
def heapSize (r : Rules := spec) : Nat := ofs + size (entries r)

def program (r : Rules := spec) (m : Mutant := .none) : List PFun × PFun :=
  let es := entries r
  (functions r es m, main es)

/-- The refusals in the order the program numbers them, from 1. -/
def refusals : List Refusal :=
  [.noHeader, .noSeparator, .headerTooLong, .lineTooLong, .malformed, .injected [], .traced [],
   .deprecated [], .notOffered [], .blankLine [], .badField [], .repeated [], .missing [], .posted,
   .longMessageId [], .noSender, .distributionAll, .badDate [], .dateAhead [], .datePast [],
   .tooManyGroups, .reservedGroup, .noKnownGroup]

/-- The area as a C header for the lane's host, with the reasons' names. -/
def header : String :=
  let defs : List (String × Nat) :=
    [("AT", ofs), ("INPUT", aInput), ("INPUT_MAX", artMax), ("MODE", xMode), ("LEN", xLen),
     ("WALL", xWall), ("WALL_MAX", wallMax), ("SEQ", xSeq), ("RUN", xRun), ("CONN", xConn),
     ("ID_LEN", xIdLen), ("ID", xId), ("ID_CAP", idCap), ("RAND_LEN", xRandLen), ("RAND", xRand),
     ("RAND_CAP", randCap), ("GROUPS_N", xGroupsN), ("GROUPS", xGroups), ("GROUP_SIZE", groupSize),
     ("GROUPS_CAP", groupsCap), ("VERDICT", xVerdict), ("NAME_LEN", xNameLen), ("NAME", xName),
     ("NAME_CAP", nameCap), ("OUT_LEN", xOutLen), ("OUT", xOut), ("OUT_MAX", outMax),
     ("MSG_LEN", xMsgLen), ("MSG", xMsg), ("MSG_CAP", msgCap), ("KNOWN_N", xKnownN), ("KNOWN", xKnown),
     ("KNOWN_MAX", knownMax), ("VALUE", xValue), ("AREA", size (entries spec)), ("REFUSALS", refusals.length)]
  "/* Generated by dn-compiler emit-article-layout from DN.News.ArticleProg. */\n" ++
  "#ifndef DN_ARTICLE_LAYOUT_H\n#define DN_ARTICLE_LAYOUT_H\n" ++
  String.join (defs.map fun (name, value) => s!"#define DN_ARTICLE_{name} {value}\n") ++
  "#define DN_ARTICLE_REASONS " ++
    ", ".intercalate (refusals.map fun x => "\"" ++ (ArticleModel.reason x).1 ++ "\"") ++ "\n" ++
  "#endif\n"

/-- Whether the analysis of decision 0004 accepts the program, its heap the header and the area. -/
def accepted (m : Mutant) : Bool :=
  let (fs, f) := program spec m
  match fs.mapM (fun g => (Lower.lower g).map (g.name, g.params.map (·.2), ·)), Lower.lower f with
  | some fns, some p => (Analyzer.checkProgram (heapSize spec) fns p).toBool
  | _, _ => false

/-- The analysis accepts the program, and refuses it when a copy does not check where it reads. -/
def regression_964 (_ : Unit) : Bool := accepted .none && !accepted .unkept

/-- The area fits the heap the hosts give a program, the input the grammar's, and the names the
tables: `artClass` reads at most 64 octets of a name. The input takes the header section the session
checks, at most two octets past the bound (`PostSpec.frameOctet_adds`). -/
def regression_965 : Bool :=
  heapSize spec ≤ 1024 * 1024 && artMax ≤ AbnfProg.inputRoom && X % 8 == 0 &&
    spec.headerMax + 2 ≤ artMax &&
    (entries spec).all (·.length ≤ 64) && refusals.length == 23

end DN.News.ArticleProg
