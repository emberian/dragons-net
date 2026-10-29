-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.SessionSpec

/-!
# DN.News.SessionMutant

The session of `DN.News.SessionSpec` with one of its rules broken, for the lane that holds the
session against an independent reference to show that it sees each (`scripts/session_check.py`).
A rule of the store's side is broken by its field of `DN.News.PostSpec.Rules` (`rulesOf`). With no
rule broken it is the specification (`turnM_none`, `settleM_none`, `deadlineM_none`).
-/

namespace DN.News.SessionMutant

open DN.News.FrameSpec DN.News.Framer DN.News.CommandSpec DN.News.SessionSpec
open DN.News.PostSpec (Store Slot Job Done Rules)

inductive Mutant
  | none
  /-- bytes received start the line's deadline again -/
  | lineRenewed
  /-- no deadline for the rest of a line -/
  | noLineDeadline
  /-- the line's deadline runs while output is untaken -/
  | lineWhileBusy
  /-- output taken does not count as activity -/
  | idleNotRenewed
  /-- a send of which nothing was taken counts as activity -/
  | zeroTakeCounts
  /-- a line that gets no reply counts as a command -/
  | blankCounts
  /-- the first command does not clear its deadline -/
  | firstNotCleared
  /-- reading stops for good once a command is answered -/
  | readNotResumed
  /-- no greeting -/
  | noGreeting
  /-- events of an older generation are applied -/
  | staleApplied
  /-- the end of input is not acted on -/
  | endIgnored
  /-- untaken output is sent again without waiting for the host -/
  | resendAnytime
  /-- the next turn earlier than the earliest deadline -/
  | wakeEarly
  /-- a line answered while output is untaken -/
  | answerWhileBusy
  /-- lines after a QUIT answered -/
  | quitTail
  /-- an article's octets start its deadline again -/
  | articleRenewed
  /-- no deadline for an article -/
  | noArticleDeadline
  /-- the deadlines run while a POST waits for a slot -/
  | waitDeadlines
  /-- a connection that may not post greeted with 200 -/
  | greetAll
  /-- a POST answered 340 once the store has stopped accepting -/
  | postAfterStop
  /-- a POST of a connection greeted with 201 answered 340 -/
  | postUnpermitted
  /-- POST listed among the capabilities once the store has stopped accepting -/
  | capabilitiesStale
  /-- the host never told to read, or not, with nothing to send -/
  | noReadControl
  /-- a fifth POST at once -/
  | fifthPost
  /-- an article one octet longer -/
  | articleLonger
  /-- no dot put before a line of the file that starts with one -/
  | unstuffed
  /-- a Message-ID another slot has reserved taken -/
  | reservedTaken
  /-- the file closed without a sync -/
  | noFileSync
  /-- the directory not synced after the rename -/
  | noDirSync
  /-- the journal not synced after the append -/
  | noJournalSync
  /-- two syncs of the directory in flight -/
  | dirSyncsOverlap
  /-- two appends of the journal in flight -/
  | appendsOverlap
  /-- an article's number not above the group's highest -/
  | numbersNotAbove
  /-- a failed sync does not stop the store accepting -/
  | syncFailureIgnored
  /-- a failed append of the journal answered 441 -/
  | unknownAnswered
  /-- a refused article's names left -/
  | namesLeft
  /-- a block that ends before the empty line not refused -/
  | unseparated
  /-- one article more than the store holds -/
  | capacityOver
  /-- a refused article's Message-ID still reserved -/
  | refusedReserves
  /-- the articles in flight not refused once the store stops -/
  | stopSparesFlight
  /-- a commit whose sync completes after the store stopped answered 240 -/
  | commitAfterStop
  /-- a POST that waits not answered 403 once the store stops -/
  | waitThroughStop
  /-- a free slot given to the waiting POST of the lowest index, not the first that came -/
  | lowestFirst
  /-- a ninth read at once -/
  | ninthRead
  /-- a file's lines not checked as it is read -/
  | linesUnchecked
  /-- a file's CRC-32C not checked -/
  | crcUnchecked
  /-- a file longer than its commit says read as if it ended there -/
  | longerServed
  /-- no Xref in ARTICLE and HEAD -/
  | noXref
  /-- the 220, 221 or 222 line given before anything of the file is checked -/
  | statusEarly
  /-- a free read given to the waiting connection of the lowest index, not the first that came -/
  | readLowestFirst
  /-- inactivity running while a read has nothing to give -/
  | idleWhileFetching
  /-- the host told to read while a read answers the connection -/
  | readWhileFetching
  /-- a file taken as whole once its commit's size is read, with nothing read past it -/
  | endUnsought
  /-- the empty line not looked for where the commit says the header section ends -/
  | headerUnchecked
  /-- a job slot a read's job holds given to another job -/
  | jobsShared
  /-- a file a failed read or a connection gone leaves open never closed -/
  | leftOpen
  /-- GROUP leaves the current article as it was -/
  | groupKeepsCurrent
  /-- GROUP of an empty group leaves the current article as it was -/
  | emptyKeepsCurrent
  /-- a GROUP answered 411 leaves no group selected -/
  | unknownDeselects
  /-- an article found by number not made current -/
  | numberKeepsCurrent
  /-- an article found by message-id made current when the selected group holds it -/
  | idMoves
  /-- NEXT may stay on the current article -/
  | nextInclusive
  /-- LAST may stay on the current article -/
  | lastInclusive
  /-- NEXT and LAST answer without moving -/
  | moveStays
  /-- a number found in another group when the selected one lacks it -/
  | numberAnyGroup
  /-- groups named without regard to case -/
  | groupCaseless
  /-- a number with no group selected answered 423 -/
  | numberWithoutGroup
  /-- octets past US-ASCII taken in a group's name whatever they are -/
  | utf8Unchecked
  /-- a group's name of any bytes -/
  | groupNameUnchecked
  /-- an article to be read by its number made current before the read answers, so after a 403 -/
  | unreadMoves
  /-- LISTGROUP leaves the current article as it was -/
  | listgroupKeepsCurrent
  /-- LISTGROUP lists the articles the store takes after the group is selected -/
  | listgroupLater
  /-- LISTGROUP lists all the group's articles whatever its range -/
  | rangeIgnored
  /-- the last number of a range left out -/
  | rangeEndExclusive
  /-- the leftmost pattern of a wildmat that matches decides -/
  | wildmatLeftmost
  /-- a negated pattern that matches taken as a match -/
  | negationIgnored
  /-- LIST ACTIVE gives a group's lowest number before its highest -/
  | marksSwapped
  /-- LIST ACTIVE gives `y` once the store has stopped accepting -/
  | statusFixed
  /-- LIST without a keyword answered as LIST NEWSGROUPS -/
  | listDefaultNewsgroups
  /-- LIST's keywords compared with regard to case -/
  | listKeywordCased
  /-- a wildmat's first pattern negated -/
  | firstNegated
  /-- DATE gives the host's monotonic clock -/
  | dateMonotonic
  /-- DATE takes the wall clock for seconds -/
  | dateUnits
  /-- NEWGROUPS takes any six or eight digits for a date and any six for a time -/
  | newgroupsUnchecked
  /-- a part of a listing one octet longer than an action -/
  | partLonger
  /-- the host told to read while a listing goes out -/
  | listingReads
  /-- `*` taking one character or more -/
  | starNonEmpty
  /-- a pattern matching a name it takes the start of -/
  | wildmatUnanchored
  /-- a pattern's characters compared without regard to case -/
  | wildmatCaseless
  /-- the line of a group that does not fit a part left out -/
  | groupLineDropped
  /-- the terminating line put in a part it does not fit -/
  | endForced
  /-- DATE's day, hour, minute and second without the zero before one digit -/
  | dateUnpadded
  /-- the line's deadline running while a listing goes out -/
  | lineWhileListing
  /-- READER left out of the capabilities of a server with a store, to a connection that may not post -/
  | readerUnadvertised
  /-- READER among the capabilities of a server without a store -/
  | readerWithoutStore
  /-- MODE READER answered 200 once the store has stopped accepting -/
  | modeStale
  /-- MODE READER leaves no group selected -/
  | modeDeselects
  /-- the connection kept open after MODE READER's 502 -/
  | refusedStaysOpen
  /-- MODE READER answered 200 to a connection greeted with 201 -/
  | modeUngreeted
  /-- XOVER takes a message-id, as OVER does -/
  | xoverById
  /-- HDR gives any metadata item, as empty -/
  | metadataServed
  /-- HDR takes a field whose name holds a colon -/
  | fieldColon
  /-- LIST OVERVIEW.FMT answered with an argument -/
  | overviewFmtArgs
  /-- LIST HEADERS answered with any argument -/
  | headersAnyArg
  /-- OVER and HDR by message-id give the article's number in the selected group -/
  | idNumbered
  /-- the last number of an OVER's or HDR's range left out -/
  | overRangeExclusive
  /-- XOVER and XHDR of an empty range answered 423 -/
  | legacyEmptyRefused
  /-- OVER and HDR of an empty range answered with an empty list -/
  | overEmptyListed
  /-- OVER and HDR make the article current -/
  | overMoves
  /-- a field's lines kept apart -/
  | foldsKept
  /-- a TAB in a field kept -/
  | tabsKept
  /-- fields named with regard to case -/
  | fieldsCased
  /-- the last field of a name taken -/
  | lastField
  /-- the SP after a field's colon kept -/
  | spaceKept
  /-- `:bytes` counting the dots put before lines -/
  | bytesStuffed
  /-- `:bytes` without Xref -/
  | bytesWithoutXref
  /-- `:lines` counting the header section's lines too -/
  | linesWhole
  /-- the overview line without Xref -/
  | overviewWithoutXref
  /-- no HDR line for an article that lacks the field -/
  | absentDropped
  /-- an XHDR line for an article that lacks the field -/
  | absentListed
  /-- XHDR's line of an article named by its message-id labelled 0 -/
  | xhdrNumbered
  /-- an overview read taking a header section one octet longer than the program's buffer -/
  | overviewLonger
  /-- an overview line given once the header section is read, before the rest is checked -/
  | overviewEarly
  /-- 224, 225 or 221 before each article's line -/
  | statusRepeated
  /-- an overview read failing at a later article answered 403 -/
  | viewFailureAnswered
  /-- a range of OVER or HDR taking the group's articles above its last, those the store takes after
  the line is answered among them -/
  | rangeLater
  /-- the dot put before a header line that starts with one kept in its name -/
  | headerStuffed
  /-- Xref in the overview line folded as ARTICLE gives it -/
  | xrefFolded
  /-- metadata items named with regard to case -/
  | metadataCased
  /-- an overview read failing at its first article closing the connection -/
  | firstFailureClosed
  /-- HDR of a metadata item it does not give answered 412 with no group selected -/
  | refusedAfterGroup
  deriving DecidableEq, Repr

def names : List (String × Mutant) :=
  [("line-renewed", .lineRenewed), ("no-line-deadline", .noLineDeadline),
   ("line-while-busy", .lineWhileBusy), ("idle-not-renewed", .idleNotRenewed),
   ("zero-take-counts", .zeroTakeCounts), ("blank-counts", .blankCounts),
   ("first-not-cleared", .firstNotCleared),
   ("read-not-resumed", .readNotResumed), ("no-greeting", .noGreeting),
   ("stale-applied", .staleApplied), ("end-ignored", .endIgnored),
   ("resend-anytime", .resendAnytime), ("wake-early", .wakeEarly),
   ("answer-while-busy", .answerWhileBusy), ("quit-tail", .quitTail),
   ("article-renewed", .articleRenewed), ("no-article-deadline", .noArticleDeadline),
   ("wait-deadlines", .waitDeadlines), ("greet-all", .greetAll),
   ("post-after-stop", .postAfterStop), ("post-unpermitted", .postUnpermitted),
   ("capabilities-stale", .capabilitiesStale), ("no-read-control", .noReadControl),
   ("fifth-post", .fifthPost), ("article-longer", .articleLonger), ("unstuffed", .unstuffed),
   ("reserved-taken", .reservedTaken),
   ("no-file-sync", .noFileSync), ("no-dir-sync", .noDirSync),
   ("no-journal-sync", .noJournalSync), ("dir-syncs-overlap", .dirSyncsOverlap),
   ("appends-overlap", .appendsOverlap), ("numbers-not-above", .numbersNotAbove),
   ("sync-failure-ignored", .syncFailureIgnored), ("unknown-answered", .unknownAnswered),
   ("names-left", .namesLeft), ("unseparated", .unseparated), ("capacity-over", .capacityOver),
   ("refused-reserves", .refusedReserves), ("stop-spares-flight", .stopSparesFlight),
   ("commit-after-stop", .commitAfterStop), ("wait-through-stop", .waitThroughStop),
   ("lowest-first", .lowestFirst), ("ninth-read", .ninthRead), ("lines-unchecked", .linesUnchecked),
   ("crc-unchecked", .crcUnchecked), ("longer-served", .longerServed), ("no-xref", .noXref),
   ("status-early", .statusEarly), ("read-lowest-first", .readLowestFirst),
   ("idle-while-fetching", .idleWhileFetching), ("read-while-fetching", .readWhileFetching),
   ("end-unsought", .endUnsought), ("header-unchecked", .headerUnchecked), ("jobs-shared", .jobsShared),
   ("left-open", .leftOpen), ("group-keeps-current", .groupKeepsCurrent),
   ("empty-keeps-current", .emptyKeepsCurrent), ("unknown-deselects", .unknownDeselects),
   ("number-keeps-current", .numberKeepsCurrent), ("id-moves", .idMoves),
   ("next-inclusive", .nextInclusive), ("last-inclusive", .lastInclusive), ("move-stays", .moveStays),
   ("number-any-group", .numberAnyGroup), ("group-caseless", .groupCaseless),
   ("number-without-group", .numberWithoutGroup), ("utf8-unchecked", .utf8Unchecked),
   ("group-name-unchecked", .groupNameUnchecked), ("unread-moves", .unreadMoves),
   ("listgroup-keeps-current", .listgroupKeepsCurrent), ("listgroup-later", .listgroupLater),
   ("range-ignored", .rangeIgnored), ("range-end-exclusive", .rangeEndExclusive),
   ("wildmat-leftmost", .wildmatLeftmost),
   ("negation-ignored", .negationIgnored), ("marks-swapped", .marksSwapped), ("status-fixed", .statusFixed),
   ("list-default-newsgroups", .listDefaultNewsgroups), ("list-keyword-cased", .listKeywordCased),
   ("first-negated", .firstNegated), ("date-monotonic", .dateMonotonic), ("date-units", .dateUnits),
   ("newgroups-unchecked", .newgroupsUnchecked), ("part-longer", .partLonger),
   ("listing-reads", .listingReads), ("star-non-empty", .starNonEmpty),
   ("wildmat-unanchored", .wildmatUnanchored), ("wildmat-caseless", .wildmatCaseless),
   ("group-line-dropped", .groupLineDropped), ("end-forced", .endForced), ("date-unpadded", .dateUnpadded),
   ("line-while-listing", .lineWhileListing), ("reader-unadvertised", .readerUnadvertised),
   ("reader-without-store", .readerWithoutStore), ("mode-stale", .modeStale), ("mode-deselects", .modeDeselects),
   ("refused-stays-open", .refusedStaysOpen), ("mode-ungreeted", .modeUngreeted),
   ("xover-by-id", .xoverById), ("metadata-served", .metadataServed), ("field-colon", .fieldColon),
   ("overview-fmt-args", .overviewFmtArgs), ("headers-any-arg", .headersAnyArg), ("id-numbered", .idNumbered),
   ("over-range-exclusive", .overRangeExclusive), ("legacy-empty-refused", .legacyEmptyRefused),
   ("over-empty-listed", .overEmptyListed), ("over-moves", .overMoves), ("folds-kept", .foldsKept),
   ("tabs-kept", .tabsKept), ("fields-cased", .fieldsCased), ("last-field", .lastField),
   ("space-kept", .spaceKept), ("bytes-stuffed", .bytesStuffed), ("bytes-without-xref", .bytesWithoutXref),
   ("lines-whole", .linesWhole), ("overview-without-xref", .overviewWithoutXref),
   ("absent-dropped", .absentDropped), ("absent-listed", .absentListed), ("xhdr-numbered", .xhdrNumbered),
   ("overview-longer", .overviewLonger), ("overview-early", .overviewEarly),
   ("status-repeated", .statusRepeated), ("view-failure-answered", .viewFailureAnswered),
   ("range-later", .rangeLater), ("header-stuffed", .headerStuffed), ("xref-folded", .xrefFolded),
   ("metadata-cased", .metadataCased), ("first-failure-closed", .firstFailureClosed),
   ("refused-after-group", .refusedAfterGroup)]

/-- The store's rules with the mutant's broken. -/
def rulesOf : Mutant → Rules
  | .fifthPost => { posts := 5 }
  | .articleLonger => { articleMax := 1000001 }
  | .unstuffed => { stuffs := false }
  | .reservedTaken => { reserves := false }
  | .noFileSync => { syncsFile := false }
  | .noDirSync => { syncsDir := false }
  | .noJournalSync => { syncsJournal := false }
  | .dirSyncsOverlap => { oneDirSync := false }
  | .appendsOverlap => { oneAppend := false }
  | .numbersNotAbove => { numbersAbove := false }
  | .syncFailureIgnored => { stops := false }
  | .unknownAnswered => { unknown := false }
  | .namesLeft => { cleans := false }
  | .unseparated => { separates := false }
  | .capacityOver => { capacity := Recovery.capacity + 1 }
  | .refusedReserves => { releases := false }
  | .stopSparesFlight => { refusesInFlight := false }
  | .commitAfterStop => { distrusts := false }
  | .ninthRead => { reads := 9 }
  | .linesUnchecked => { checksLines := false }
  | .crcUnchecked => { checksCrc := false }
  | .longerServed => { checksSize := false }
  | .noXref => { xref := false }
  | .statusEarly => { statusLate := false }
  | .endUnsought => { seeksEnd := false }
  | .headerUnchecked => { checksHeader := false }
  | .jobsShared => { readJobsApart := false }
  | .leftOpen => { closesAfter := false }
  | .foldsKept => { overview := { unfolds := false } }
  | .tabsKept => { overview := { spaces := false } }
  | .fieldsCased => { overview := { caseless := false } }
  | .lastField => { overview := { firstField := false } }
  | .spaceKept => { overview := { dropsSpace := false } }
  | .bytesStuffed => { overview := { unstuffed := false } }
  | .bytesWithoutXref => { overview := { countsXref := false } }
  | .linesWhole => { overview := { bodyOnly := false } }
  | .overviewWithoutXref => { overview := { xrefField := false } }
  | .absentDropped => { overview := { keepsAbsent := false } }
  | .absentListed => { overview := { skipsAbsent := false } }
  | .xhdrNumbered => { overview := { labelsId := false } }
  | .overviewLonger => { overviewMax := 69633 }
  | .overviewEarly => { overviewWhole := false }
  | .headerStuffed => { overview := { unstuffsHeader := false } }
  | .xrefFolded => { overview := { unfoldsXref := false } }
  | .metadataCased => { overview := { metaCaseless := false } }
  | _ => {}

def freshM (m : Mutant) (i : Identity) (greeted : Bool) (number gen now : Nat) : Conn :=
  { Conn.fresh i greeted number gen now with
    out := if m = .noGreeting then [] else (Conn.fresh i greeted number gen now).out }

def liveM (m : Mutant) (t : Table) (idx gen : Nat) : Option Conn :=
  match t[idx]? with
  | some (some c) => if c.gen = gen || m = .staleApplied then some c else none
  | _ => none

def applyEventM (m : Mutant) (i : Identity) (now : Nat) (s : Server) :
    Event → Except Breach Server
  | .opened idx gen mayPost => do
    checkIndex idx
    match s.table[idx]? with
    | some (some _) => throw .reopened
    | _ =>
      if gen ≤ s.gens.getD idx 0 || genLimit < gen then throw .reopened
      else
        let c := freshM m i (greets s.store (mayPost || m = .greetAll)) (s.opened + 1) gen now
        return { s with table := s.table.set idx (some c), opened := s.opened + 1,
                        gens := s.gens.set idx gen }
  | .received idx gen data => do
    checkIndex idx
    if chunk < data.length then throw .tooLong
    match liveM m s.table idx gen with
    | some c =>
      if c.asked then
        let due := if m = .lineRenewed then 0 else c.lineDue
        return { s with table := s.table.set idx (some { c with held := data, lineDue := due }) }
      else throw .unasked
    | none => return s
  | .writable idx gen => do
    checkIndex idx
    match liveM m s.table idx gen with
    | some c => return { s with table := s.table.set idx (some { c with blocked := false }) }
    | none => return s
  | .inputEnded idx gen => do
    checkIndex idx
    match liveM m s.table idx gen with
    | some c =>
      if c.asked then
        if m = .endIgnored then return s
        else
          let c' := { c with phase := .ending, lineDue := 0, post := none, articleDue := 0,
                             want := none, read := none, view := none }
          return { s with
            table := s.table.set idx (some c'),
            store := s.store.map (Store.abandon idx gen) }
      else throw .unasked
    | none => return s
  | .closed idx gen => do
    checkIndex idx
    match liveM m s.table idx gen with
    | some _ =>
      return { s with table := s.table.set idx none, store := s.store.map (Store.abandon idx gen) }
    | none => return s

def wantsWithM (m : Mutant) (st : Option Store) (c : Conn) : Bool :=
  (c.wantsWith st || (m = .readWhileFetching && c.read.isSome && c.wants && !c.waiting) ||
      (m = .listingReads && { c with listing := none }.wantsWith st)) &&
    !(m = .readNotResumed && c.first == 0)

def waitLineM (m : Mutant) (now : Nat) (c : Conn) : Conn :=
  if (c.out.isEmpty || m = .lineWhileBusy) && c.phase == .open_ && c.line != .fresh &&
      c.want.isNone && (c.listing.isNone || m = .lineWhileListing) && m != .noLineDeadline then
    if c.lineDue == 0 then { c with lineDue := now + lineTime } else c
  else { c with lineDue := 0 }

/-- A wildmat whose first pattern may be negated too. -/
def wildmatFirstNegated (w : List Byte) : Option Wildmat := do
  match (← chars w).splitOn (ascii ",") with
  | first :: rest => return (← patternOf true first) :: (← rest.mapM (patternOf true))
  | [] => none

/-- What HDR's or XHDR's arguments after the field name, if they name articles. -/
def selOfArgs : List (List Byte) → Option Sel
  | [] => some .current
  | [a] => if isMessageId a then some (.id a) else (range? a).map fun (lo, hi) => .range lo hi
  | _ => none

/-- LIST's, NEWGROUPS's, XOVER's and HDR's arguments as the mutant's rule takes them. -/
def readerReplyM (m : Mutant) (r : Reply) (c : Option Cmd) (args : List (List Byte)) : Reply :=
  match c, args with
  | some .list, [] => if m = .listDefaultNewsgroups then .newsgroups else r
  | some .list, [k, _] =>
    if m = .overviewFmtArgs && k.map upper = ascii "OVERVIEW.FMT" then .overviewFmt
    else if m = .headersAnyArg && k.map upper = ascii "HEADERS" then .headerList
    else readerListM m r k [args.getLast!]
  | some .list, k :: rest => readerListM m r k rest
  | some .xover, [a] => if m = .xoverById && isMessageId a then .over true (.id a) else r
  | some .hdr, f :: rest | some .xhdr, f :: rest =>
    match selOfArgs rest with
    | some sel =>
      if (m = .metadataServed && r = .fieldRefused) ||
          (m = .fieldColon && r = .syntax && f.head? != some 58#8 && f.all fun b => isNotColon b || b == 58#8) then
        .hdr (c == some .xhdr) f sel
      else r
    | none => r
  | some .newgroups, d :: t :: rest =>
    if m = .newgroupsUnchecked && r = .syntax && d.all isDigit && (d.length == 6 || d.length == 8) &&
        t.all isDigit && t.length == 6 && (rest.isEmpty || rest.map (·.map upper) == [ascii "GMT"])
    then .newGroups else r
  | _, _ => r
where
  readerListM (m : Mutant) (r : Reply) (k : List Byte) (rest : List (List Byte)) : Reply :=
    if m = .listKeywordCased && k != ascii "ACTIVE" && k != ascii "NEWSGROUPS" && k != ascii "OVERVIEW.FMT" &&
        k != ascii "HEADERS" then .syntax
    else if m = .firstNegated && r = .syntax then
      match rest with
      | [x] =>
        match wildmatFirstNegated x with
        | some w =>
          if k.map upper = ascii "ACTIVE" then .active (some w)
          else if k.map upper = ascii "NEWSGROUPS" then .newsgroups else r
        | none => r
      | _ => r
    else r

/-- A GROUP's name taken without its check, or with octets past US-ASCII unchecked; LIST's and
NEWGROUPS's arguments as `readerReplyM` takes them. -/
def replyInM (m : Mutant) (offered : Bool) (l : Line) : Reply :=
  match replyIn offered l, words l.kept with
  | .syntax, [w, g] =>
    if offered && l.kind == .command && commandIn offered w == some .group && !g.isEmpty &&
        (m = .groupNameUnchecked || (m = .utf8Unchecked && g.all fun b => 128 ≤ b.toNat || isExactAscii b))
    then (if g.length ≤ groupNameMax then .select g else .noSuchGroup)
    else if offered && l.kind == .command then readerReplyM m .syntax (commandIn offered w) [g]
    else .syntax
  | r, w :: args => if offered && l.kind == .command then readerReplyM m r (commandIn offered w) args else r
  | r, [] => r

/-- `viewOf`, an article named by its message-id given its number in the selected group by
`idNumbered`, a range's last number left out by `overRangeExclusive`, an empty range of XOVER and XHDR
answered 423 by `legacyEmptyRefused`, and of OVER and HDR with an empty list by `overEmptyListed`. -/
def viewOfM (m : Mutant) (p : Posting) (c : Conn) (lg : Bool) (f : Option (List Byte)) (s : Sel) : Reply :=
  let s := match s with
    | .range lo hi => if m = .overRangeExclusive then .range lo (hi - 1) else .range lo hi
    | s => s
  let r := viewOf p c lg f s
  match r with
  | .overview lg' f' true [(0, mid)] =>
    if m = .idNumbered then
      .overview lg' f' true [(((c.group.bind fun g => (numbered p.held g).find? (·.2 == mid)).map (·.1)).getD 0, mid)]
    else r
  | .noneOver | .noneHdr => if m = .legacyEmptyRefused then .noRange else r
  | .noRange => if m = .overEmptyListed then (if f.isSome then .noneHdr else .noneOver) else r
  | _ => r

def resolveM (m : Mutant) (p : Posting) (c : Conn) : Reply → Reply
  | .capabilities =>
    if c.greeted && (p.accepting || m = .capabilitiesStale) then .capabilitiesPost
    else if (p.offered && m != .readerUnadvertised) || m = .readerWithoutStore then .capabilitiesReader
    else .capabilities
  | .modeReader =>
    if !p.offered then .modeReader
    else if (c.greeted || m = .modeUngreeted) && (p.accepting || m = .modeStale) then .readerPosting
    else .readerNoPosting
  | .post =>
    if !c.greeted && !(m = .postUnpermitted && p.offered) then .notPermitted
    else if !p.accepting && m != .postAfterStop then .unavailable else .post
  | .select g =>
    if m = .groupCaseless then
      match p.groups.find? (·.map upper == g.map upper) with
      | some g' => summary p.held g'
      | none => .noSuchGroup
    else resolve p c (.select g)
  | .byNumber k n =>
    if m = .numberWithoutGroup && c.group.isNone then .noNumber
    else if m = .numberAnyGroup then
      match c.group with
      | none => .noGroup
      | some g =>
        (((atNumber p.held g n).orElse fun _ => p.groups.findSome? fun g' => atNumber p.held g' n).map
          (foundAs k)).getD .noNumber
    else resolve p c (.byNumber k n)
  | .move fwd =>
    if (m = .nextInclusive && fwd) || (m = .lastInclusive && !fwd) then
      match c.group with
      | none => .noGroup
      | some g =>
        if c.current = 0 then .noCurrent
        else (((if fwd then nextAfter p.held g (c.current - 1) else prevBefore p.held g (c.current + 1))).map
          fun (n, id) => .stat n id).getD (if fwd then .noNext else .noPrevious)
    else resolve p c (.move fwd)
  | .over lg s => viewOfM m p c lg none s
  | .hdr lg f s => viewOfM m p c lg (some f) s
  | .fieldRefused => if m = .refusedAfterGroup && c.group.isNone then .noGroup else .fieldRefused
  | r => resolve p c r

/-- The selected group and the current article after a reply, as `Reply.groupAfter` and
`Reply.currentAfter` have them, but for the mutant's rule. -/
def groupAfterM (m : Mutant) (r : Reply) (g : Option (List Byte)) : Option (List Byte) :=
  if (m = .unknownDeselects && r = .noSuchGroup) ||
      (m = .modeDeselects && (r = .readerPosting || r = .readerNoPosting)) then none
  else r.groupAfter g

def currentAfterM (m : Mutant) (p : Posting) (c : Conn) (asked r : Reply) : Nat :=
  match r with
  | .selected count _ _ _ =>
    if m = .groupKeepsCurrent || (m = .emptyKeepsCurrent && count = 0) then c.current
    else r.currentAfter c.current
  | .noSuchGroup => if m = .unknownDeselects then 0 else c.current
  | .listed .. => if m = .listgroupKeepsCurrent then c.current else r.currentAfter c.current
  | .stat n id | .lookup _ n id =>
    let byNumber := match asked with | .byNumber .. => true | _ => false
    let moved := match asked with | .move _ => true | _ => false
    let read := match r with | .lookup .. => true | _ => false
    if (m = .numberKeepsCurrent && byNumber) || (m = .moveStays && moved) then c.current
    else if m = .idMoves && n = 0 then
      match c.group with
      | some g => (((numbered p.held g).find? (·.2 == id)).map (·.1)).getD c.current
      | none => c.current
    else if m = .unreadMoves && read && n != 0 then n
    else r.currentAfter c.current
  | _ => r.currentAfter c.current

/-- What is left to go out after a reply's first line, but for the mutant's rule. -/
def listingOfM (m : Mutant) : Reply → Option Listing
  | .listed _ _ high g lo hi =>
    let (lo, hi) := if m = .rangeIgnored then (1, numberMax) else if m = .rangeEndExclusive then (lo, hi - 1)
      else (lo, hi)
    some (.numbers g lo (if m = .listgroupLater then hi else min hi high))
  | r => listingOf r

/-- DATE's digits with the fields after the month as they are, no zero before one digit. -/
def dateUnpaddedDigits (wall : Nat) : List Byte :=
  let secs := wall / 1000
  let date := ArticleSpec.civilFromDays (secs / 86400)
  let t := secs % 86400
  padded 4 date.1 ++ padded 2 date.2.1 ++ decimal date.2.2 ++ decimal (t / 3600) ++ decimal (t % 3600 / 60) ++
    decimal (t % 60)

/-- DATE's reply, from the clock the mutant's rule takes. -/
def dateM (m : Mutant) (p : Posting) (now : Nat) (r : Reply) : Reply :=
  match r with
  | .time _ =>
    if m = .dateMonotonic then .time (dateDigits now) else if m = .dateUnits then .time (dateDigits (p.wall * 1000))
    else if m = .dateUnpadded then .time (dateUnpaddedDigits p.wall) else r
  | _ => r

def serveM (m : Mutant) (i : Identity) (p : Posting) (now : Nat) : Nat → Conn → Conn
  | 0, c => c
  | fuel + 1, c =>
    if c.held.isEmpty then c
    else
      let (k, line', v) := frameOnce lineLimit c.line c.held
      let c1 := { c with line := line', held := c.held.drop k }
      match v with
      | none => c1
      | some l =>
        let asked := replyInM m p.offered l
        match dateM m p now (resolveM m p c asked) with
        | .ignore =>
          serveM m i p now fuel
            (if m = .blankCounts then { c1 with first := 0, idle := now + inactivity } else c1)
        | r =>
          if (!c.out.isEmpty && m != .answerWhileBusy) || c.want.isSome || c.listing.isSome then c
          else if r = .post then
            if m = .waitDeadlines then { c1 with waiting := true }
            else { c1 with waiting := true, first := 0, idle := 0 }
          else if let some (k, n, id, v) := readOf p r then
            serveM m i p now fuel
              { c1 with want := some (k, n, id), view := v, first := 0, idle := 0,
                        current := if m = .idMoves || m = .unreadMoves then currentAfterM m p c1 asked r
                          else c1.current }
          else
            let first := if m = .firstNotCleared then c1.first else 0
            let c2 := { c1 with out := text i r, first := first, idle := now + inactivity,
                                group := groupAfterM m r c1.group, current := currentAfterM m p c1 asked r,
                                listing := listingOfM m r }
            if (r = .quit && m != .quitTail) || (r = .modeReader && m != .refusedStaysOpen) then
              { c2 with phase := .quitting, held := [] }
            else serveM m i p now fuel c2

/-- `progress`, an article's octets taken renewing its deadline with `articleRenewed`. -/
def progressM (m : Mutant) (i : Identity) (now wall : Nat) (st : Option Store) (c : Conn) :
    Conn × Option Store × Bool :=
  let g := progress i now wall st c
  if m = .articleRenewed && g.1.held.length < c.held.length && g.1.articleDue != 0 then
    ({ g.1 with articleDue := now + articleTime }, g.2)
  else g

/-- `claim`, with the store taken as accepting by `postAfterStop`; a waiting POST kept waiting
once the store stops by `waitThroughStop`; the connection first among those waiting by
`lowestFirst`; and no deadline given the article by `noArticleDeadline`. -/
def claimM (m : Mutant) (i : Identity) (now idx : Nat) (st : Option Store) (c : Conn) :
    Conn × Option Store :=
  let first (st : Store) := { st with waiters := (idx, c.gen) :: st.waiters.erase (idx, c.gen) }
  let k := if m = .postAfterStop then
      let k := claim i now idx (st.map ({ · with accepting := true })) c
      (k.1, k.2.map ({ · with accepting := st.any (·.accepting) }))
    else if m = .waitThroughStop && c.waiting && st.any (!·.accepting) then (c, st)
    else if m = .lowestFirst then claim i now idx (st.map first) c
    else claim i now idx st c
  if m = .noArticleDeadline && c.post.isNone && k.1.post.isSome then
    ({ k.1 with articleDue := 0 }, k.2)
  else k

/-- The store with each overview read given the next article and nothing yet giving its first line
again. -/
def repeatFirst (s : Store) : Store :=
  { s with reads := s.reads.map (·.map fun r => match r.view with
    | some v => if r.given = 0 && !v.first then ({ r with view := some { v with first := true } }).refresh s.rules
        s.cfg.identity else r
    | none => r) }

/-- The store with the read of connection `c`, at the last article of a range it has gone on in,
given those of the selected group the store holds now above it too. -/
def laterArticles (c : Conn) (s : Store) : Store :=
  match c.read, c.group with
  | some k, some g =>
    match s.readSlot k with
    | some r =>
      match r.view with
      | some v =>
        let more := (((numbered s.articles g).filter (r.number < ·.1)).mergeSort fun a b => a.1 ≤ b.1).filterMap
          fun (n, id) => (s.find id).map (n, ·)
        if v.rest.isEmpty && !v.first && !more.isEmpty then
          s.setRead k (some ({ r with view := some { v with rest := more } }.refresh s.rules s.cfg.identity))
        else s
      | none => s
    | none => s
  | _, _ => s

/-- `progressRead`, inactivity left running while the read has nothing to give by
`idleWhileFetching`; an article read by its number not made current by `numberKeepsCurrent`; an
article of an OVER or HDR made current with its line by `overMoves`; the first line given before each
article's by `statusRepeated`; a read failing at a later article of an OVER or HDR answered 403 by
`viewFailureAnswered`, and at its first closing the connection by `firstFailureClosed`; a range
taking the articles the store takes meanwhile by `rangeLater`. -/
def progressReadM (m : Mutant) (i : Identity) (now : Nat) (st : Option Store) (c : Conn) :
    Conn × Option Store × Bool :=
  let st := if m = .rangeLater then st.map (laterArticles c) else st
  let r0 := match c.read, st with
    | some k, some s => s.readSlot k
    | _, _ => none
  let g := progressRead i now st c
  if m = .idleWhileFetching && g.1.read.isSome && g.1.idle == 0 then ({ g.1 with idle := c.idle }, g.2)
  else if m = .numberKeepsCurrent then ({ g.1 with current := c.current }, g.2)
  else if m = .overMoves then
    match r0 with
    | some r =>
      if r.view.isSome && r.given = 0 && !r.bad && r.number != 0 && c.out.isEmpty && !g.1.out.isEmpty then
        ({ g.1 with current := r.number }, g.2)
      else g
    | none => g
  else if m = .statusRepeated then (g.1, g.2.1.map repeatFirst, g.2.2)
  else if m = .viewFailureAnswered then
    match c.read, st, r0 with
    | some k, some s, some r =>
      if g.2.2 && r.bad && r.given = 0 then
        ({ c with out := text i .unreadable, read := none, want := none, view := none, idle := now + inactivity },
         some (s.setRead k (some { r with owner := none })).tidy, false)
      else g
    | _, _, _ => g
  else if m = .firstFailureClosed then
    match r0 with
    | some r => if r.view.isSome && r.bad && c.out.isEmpty && g.1.out == text i .unreadable then (c, st, true) else g
    | none => g
  else g

/-- `reach`, `*` taking one character or more by `starNonEmpty`, a character matched without regard
to case by `wildmatCaseless`. -/
def reachM (m : Mutant) (s : List (List Byte)) (from_ : List Nat) (x : Item) : List Nat :=
  match x with
  | .exact c =>
    if m = .wildmatCaseless then
      from_.filterMap fun k => if (s[k]?).any (·.map upper == c.map upper) then some (k + 1) else none
    else reach s from_ x
  | .star =>
    if m = .starNonEmpty then
      match from_.min? with
      | some k => List.range' (k + 1) (s.length - k)
      | none => []
    else reach s from_ x
  | .one => reach s from_ x

/-- `patternMatches`, a pattern that takes the start of `s` matching by `wildmatUnanchored`. -/
def patternMatchesM (m : Mutant) (s : List (List Byte)) (p : List Item) : Bool :=
  let ends := p.foldl (reachM m s) [0]
  if m = .wildmatUnanchored then !ends.isEmpty else ends.contains s.length

def decidesM (m : Mutant) (s : List (List Byte)) (r : Option Bool) (x : Bool × List Item) : Option Bool :=
  if !patternMatchesM m s x.2 then r
  else if m = .wildmatLeftmost then r.orElse fun _ => some !x.1
  else some (!x.1 || m = .negationIgnored)

/-- A wildmat matched as the mutant's rule matches it: the leftmost pattern that matches deciding, by
`wildmatLeftmost`; a negated pattern taken as a match, by `negationIgnored`. -/
def wildmatchM (m : Mutant) (w : Wildmat) (name : List Byte) : Bool :=
  match chars name with
  | some s => (w.foldl (decidesM m s) none).getD false
  | none => false

def activeLineM (m : Mutant) (p : Posting) (g : List Byte) : List Byte :=
  match summary p.held g with
  | .selected _ low high _ =>
    let (a, b) := if m = .marksSwapped then (low, high) else (high, low)
    g ++ SP :: decimal a ++ SP :: decimal b ++ SP ::
      ascii (if p.accepting || m = .statusFixed then "y" else "n") ++ crlf
  | _ => []

def nextM (m : Mutant) (p : Posting) : Listing → Option (List Byte × Listing) :=
  nextWith (wildmatchM m) (activeLineM m p) p

/-- `partWith`, the line of a group that does not fit left out by `groupLineDropped`, the terminating
line put in whether it fits or not by `endForced`. -/
def partWithM (m : Mutant) (next : Listing → Option (List Byte × Listing)) (most : Nat) :
    Nat → List Byte → Listing → List Byte × Option Listing
  | 0, acc, l => (acc, some l)
  | fuel + 1, acc, l =>
    match next l with
    | some (line, l') =>
      if acc.length + line.length ≤ most then partWithM m next most fuel (acc ++ line) l'
      else (acc, some (if m = .groupLineDropped && (match l with | .groups .. => true | _ => false) then l' else l))
    | none => if acc.length + 3 ≤ most || m = .endForced then (acc ++ ascii ".\r\n", none) else (acc, some l)

/-- `Listing.part`, of `chunk` and one more octets by `partLonger`. -/
def partM (m : Mutant) (p : Posting) : Nat → List Byte → Listing → List Byte × Option Listing :=
  partWithM m (nextM m p) (if m = .partLonger then chunk + 1 else chunk)

def progressListM (m : Mutant) (now wall : Nat) (st : Option Store) (c : Conn) : Conn :=
  match c.listing with
  | some l =>
    if !c.out.isEmpty || c.phase = .quitting then c
    else
      let (part, rest) := partM m (Posting.of wall st) (chunk + 1) [] l
      { c with out := part, listing := rest, idle := now + inactivity }
  | none => c

/-- `claimRead`, the connection first among those waiting by `readLowestFirst`. -/
def claimReadM (m : Mutant) (idx : Nat) (st : Option Store) (c : Conn) : Conn × Option Store :=
  let first (st : Store) := { st with readers := (idx, c.gen) :: st.readers.erase (idx, c.gen) }
  if m = .readLowestFirst then claimRead idx (st.map first) c else claimRead idx st c

def emitM (m : Mutant) (idx : Nat) (wants : Bool) (c : Conn) : Option Conn × Option Action :=
  if !c.out.isEmpty then
    if c.blocked && m != .resendAnytime then (some c, none)
    else (some { c with reading := wants }, some (.send idx c.gen c.out wants))
  else if c.phase = .quitting || (c.phase = .ending && c.held.isEmpty) then
    (none, some (.closeGracefully idx c.gen))
  else if c.phase = .open_ && c.reading != wants && m != .noReadControl then
    (some { c with reading := wants }, some (.send idx c.gen [] wants))
  else (some c, none)

def actM (m : Mutant) (i : Identity) (now wall idx : Nat) (st : Option Store) (c : Conn) :
    Option Conn × Option Action × Option Store :=
  if c.due now then (none, some (.closeNow idx c.gen), st.map (Store.abandon idx c.gen))
  else
    let g := progressM m i now wall st c
    if g.2.2 then (none, some (.closeNow idx c.gen), g.2.1)
    else
      let h := progressReadM m i now g.2.1 g.1
      if h.2.2 then (none, some (.closeNow idx c.gen), h.2.1.map (Store.abandon idx c.gen))
      else
        let l := progressListM m now wall h.2.1 h.1
        let c1 := if (l.out.isEmpty || m = .answerWhileBusy) && l.phase != .quitting &&
            l.post.isNone && !l.waiting && l.want.isNone && l.listing.isNone
          then serveM m i (Posting.of wall h.2.1) now (l.held.length + 1) l else l
        let st1 := if c1.waiting && !h.1.waiting then
            h.2.1.map fun st => { st with waiters := st.waiters ++ [(idx, c.gen)] }
          else if c1.want.isSome && h.1.want.isNone then
            h.2.1.map fun st => { st with readers := st.readers ++ [(idx, c.gen)] }
          else h.2.1
        let k := claimM m i now idx st1 c1
        let k := claimReadM m idx k.2 k.1
        let r := emitM m idx (wantsWithM m k.2 k.1) k.1
        (r.1.map (waitLineM m now), r.2, k.2)

def actFromM (m : Mutant) (i : Identity) (now wall : Nat) (t : Table) :
    List Nat → Option Store → List (Option Conn × Option Action) × Option Store
  | [], st => ([], st)
  | idx :: rest, st =>
    match t[idx]? with
    | some (some c) =>
      let x := actM m i now wall idx st c
      let r := actFromM m i now wall t rest x.2.2
      ((x.1, x.2.1) :: r.1, r.2)
    | _ =>
      let r := actFromM m i now wall t rest st
      ((none, none) :: r.1, r.2)

def turnM (m : Mutant) (i : Identity) (s : Server) (now wall : Nat) (events : List Event)
    (dones : List Done) : Except Breach (Server × List Action × List Job) := do
  if batch < events.length then throw .tooManyEvents
  if now < s.clock || clockLimit ≤ now || wallLimit ≤ wall then throw .badClock
  let s ← events.foldlM (applyEventM m i now) s
  let st ← completions s dones
  let r := actFromM m i now wall s.table (List.range conns) st
  let j := jobsOf r.2
  return ({ s with table := r.1.map (·.1), clock := now, store := j.1 }, r.1.filterMap (·.2), j.2)

def settleTableM (m : Mutant) (now : Nat) (t : Table) :
    List Action → List Nat → Except Breach Table
  | [], [] => pure t
  | .send idx gen data _ :: rest, n :: ns => do
    if data.length < n then throw .overTaken
    let t := match liveM m t idx gen with
      | some c =>
        let idle := if c.read.isSome && c.out.length ≤ n && m != .idleWhileFetching then 0
          else if m = .zeroTakeCounts then now + inactivity
          else if n = 0 || c.post.isSome || c.waiting || m = .idleNotRenewed then c.idle
          else now + inactivity
        t.set idx (some (waitLineM m now
          { c with out := c.out.drop n, idle := idle, blocked := decide (n < data.length) }))
      | none => t
    settleTableM m now t rest ns
  | .send .. :: _, [] => throw .overTaken
  | _ :: rest, ns => settleTableM m now t rest ns
  | [], _ :: _ => throw .overTaken

def settleM (m : Mutant) (s : Server) (actions : List Action) (taken : List Nat) :
    Except Breach Server := do
  return { s with table := ← settleTableM m s.clock s.table actions taken }

def deadlineM (m : Mutant) (s : Server) : Nat :=
  let d := deadline s
  if m = .wakeEarly && s.clock + 1 < d then d - 1 else d

/-! ## With no rule broken, the specification -/

theorem rulesOf_none : rulesOf .none = {} := rfl

theorem freshM_none : freshM .none = Conn.fresh := by
  funext i g number gen now
  rfl

theorem liveM_none : liveM .none = Table.live := by
  funext t idx gen
  cases h : t[idx]? with
  | none => simp [liveM, Table.live, h]
  | some o => cases o <;> simp [liveM, Table.live, h]

theorem waitLineM_none : waitLineM .none = Conn.waitLine := by
  funext now c
  simp [waitLineM, Conn.waitLine]

theorem wantsWithM_none : wantsWithM .none = Conn.wantsWith := by
  funext st c
  simp [wantsWithM]

theorem readerListM_none (r : Reply) (k : List Byte) (rest : List (List Byte)) :
    readerReplyM.readerListM .none r k rest = r := by
  unfold readerReplyM.readerListM
  simp

theorem readerReplyM_none (r : Reply) (c : Option Cmd) (args : List (List Byte)) :
    readerReplyM .none r c args = r := by
  unfold readerReplyM
  split <;> simp [readerListM_none] <;> split <;> simp

theorem replyInM_none : replyInM .none = replyIn := by
  funext offered l
  unfold replyInM
  split <;> simp_all [readerReplyM_none]

theorem viewOfM_none (p : Posting) (c : Conn) (lg : Bool) (f : Option (List Byte)) (s : Sel) :
    viewOfM .none p c lg f s = viewOf p c lg f s := by
  have hs : (match s with
      | .range lo hi => if Mutant.none = .overRangeExclusive then Sel.range lo (hi - 1) else .range lo hi
      | s => s) = s := by
    cases s <;> rfl
  simp only [viewOfM, hs]
  split <;> simp_all

theorem resolveM_none : resolveM .none = resolve := by
  funext p c r
  cases r <;> simp [resolveM, resolve, viewOfM_none]

theorem groupAfterM_none : groupAfterM .none = Reply.groupAfter := by
  funext r g
  simp [groupAfterM]

theorem currentAfterM_none (p : Posting) (c : Conn) (asked r : Reply) :
    currentAfterM .none p c asked r = r.currentAfter c.current := by
  unfold currentAfterM
  split <;> simp [Reply.currentAfter]

theorem listingOfM_none : listingOfM .none = listingOf := by
  funext r
  cases r <;> simp [listingOfM, listingOf]

theorem dateM_none (p : Posting) (now : Nat) (r : Reply) : dateM .none p now r = r := by
  unfold dateM
  split <;> simp

theorem reachM_none : reachM .none = reach := by
  funext s from_ x
  cases x <;> simp [reachM]

theorem patternMatchesM_none : patternMatchesM .none = patternMatches := by
  funext s p
  simp [patternMatchesM, patternMatches, reachM_none]

theorem decidesM_none : decidesM .none = decides := by
  funext s r x
  unfold decidesM decides
  rw [patternMatchesM_none]
  split <;> simp_all

theorem wildmatchM_none : wildmatchM .none = wildmatch := by
  funext w name
  cases h : chars name <;> simp [wildmatchM, wildmatch, decidesM_none, h]

theorem activeLineM_none : activeLineM .none = activeLine := by
  funext p g
  cases h : summary p.held g <;> simp [activeLineM, activeLine, h]

theorem nextM_none : nextM .none = Listing.next := by
  funext p
  simp [nextM, Listing.next, wildmatchM_none, activeLineM_none]

theorem partWithM_none : partWithM .none = partWith := by
  funext next most fuel acc l
  induction fuel generalizing acc l with
  | zero => rfl
  | succ fuel ih =>
    simp only [partWithM, partWith]
    cases next l with
    | none => simp
    | some x => obtain ⟨line, l'⟩ := x; simp [ih]

theorem partM_none : partM .none = Listing.part := by
  funext p
  simp [partM, Listing.part, nextM_none, partWithM_none]

theorem progressListM_none : progressListM .none = progressList := by
  funext now wall st c
  cases h : c.listing <;> simp [progressListM, progressList, partM_none, h]

theorem serveM_none (i : Identity) (p : Posting) (now : Nat) :
    serveM .none i p now = serve i p now := by
  funext fuel c
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    have h1 : (Mutant.none != Mutant.answerWhileBusy) = true := rfl
    have h2 : (Mutant.none != Mutant.quitTail) = true := rfl
    have h3 : (Mutant.none != Mutant.refusedStaysOpen) = true := rfl
    simp only [serveM, serve, ih, resolveM_none, replyInM_none, groupAfterM_none, currentAfterM_none,
      dateM_none, listingOfM_none, reduceCtorEq, if_false, h1, h2, h3, Bool.and_true, Bool.or_eq_true,
      decide_eq_true_eq]
    rfl

theorem progressM_none : progressM .none = progress := by
  funext i now wall st c
  simp [progressM]

theorem claimM_none : claimM .none = claim := by
  funext i now idx st c
  simp [claimM]

theorem progressReadM_none : progressReadM .none = progressRead := by
  funext i now st c
  simp [progressReadM]

theorem claimReadM_none : claimReadM .none = claimRead := by
  funext idx st c
  simp [claimReadM]

theorem emitM_none : emitM .none = emit := by
  funext idx w c
  simp [emitM, emit]

theorem applyEventM_none : applyEventM .none = applyEvent := by
  funext i now s e
  cases e <;> simp only [applyEventM, applyEvent, liveM_none, freshM_none, reduceCtorEq,
    if_false, Bool.or_false, decide_false] <;> rfl

theorem actM_none : actM .none = act := by
  funext i now wall idx st c
  simp [actM, act, emitM_none, serveM_none, waitLineM_none, progressM_none, claimM_none,
    wantsWithM_none, progressReadM_none, claimReadM_none, progressListM_none]

theorem actFromM_none (i : Identity) (now wall : Nat) (t : Table) :
    actFromM .none i now wall t = actFrom i now wall t := by
  funext l st
  induction l generalizing st with
  | nil => rfl
  | cons idx rest ih =>
    simp only [actFromM, actFrom, ih, actM_none]
    rfl

theorem turnM_none : turnM .none = turn := by
  funext i s now wall evs ds
  simp only [turnM, turn, applyEventM_none, actFromM_none]

theorem settleTableM_none (now : Nat) : settleTableM .none now = settleTable now := by
  funext t acts ns
  induction acts generalizing t ns with
  | nil => cases ns <;> rfl
  | cons a rest ih =>
    have h : (Mutant.none != Mutant.idleWhileFetching) = true := rfl
    cases a <;> cases ns <;>
      simp only [settleTableM, settleTable, ih, liveM_none, waitLineM_none, reduceCtorEq,
        ↓reduceIte, decide_false, Bool.or_false, h, Bool.and_true] <;> rfl

theorem settleM_none : settleM .none = settle := by
  funext s acts ns
  simp [settleM, settle, settleTableM_none]

theorem deadlineM_none : deadlineM .none = deadline := by
  funext s
  simp [deadlineM]

end DN.News.SessionMutant
