(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(*
  The tree a theorem `parse_topdecs_to_ast text = INL decls` gives, written as JSON for
  scripts/parse_check.py: each constructor application a list of its name and its arguments, a
  string or a name a JSON string, a number or a word its value, T and F booleans. Only what a
  closed term built of constructors holds is written, a record as an object of its fields and a
  string made by `implode` as the string; anything else fails, and so does a parse
  that was refused or a theorem that rests on an oracle (the tag of the theories it was evaluated
  from aside).
*)
structure dnParseShowLib =
struct

open HolKernel boolLib

fun escaped s =
  String.translate
    (fn #"\"" => "\\\"" | #"\\" => "\\\\"
      | c => if Char.ord c < 32 orelse Char.ord c > 126
             then "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (Char.ord c))
             else String.str c) s

(* The fields a record's updates of ARB set, outermost first: `<| f := x; ... |>` is
   `f_fupd (K x) (...)`, the update named after the record's type and the field. *)
fun fields tm =
  if is_arb tm then []
  else
    case strip_comb tm of
      (f, [k, rest]) =>
        let
          val name = #Name (dest_thy_const f)
          val field = List.last (String.fields (fn c => c = #".") name)
          val (kc, kargs) = strip_comb k
        in
          if String.isSuffix "_fupd" field andalso #Name (dest_thy_const kc) = "K" andalso length kargs = 1
          then (String.extract (field, 0, SOME (size field - 5)), hd kargs) :: fields rest
          else raise ERR "fields" ("not a field's update: " ^ name)
        end
    | _ => raise ERR "fields" ("not a record: " ^ term_to_string tm)

fun is_record tm =
  let val (f, args) = strip_comb tm
  in length args = 2 andalso String.isSuffix "_fupd" (#Name (dest_thy_const f))
  end handle HOL_ERR _ => false

fun write out tm =
  if is_record tm then
    (TextIO.output (out, "{");
     ignore (List.foldl (fn ((field, x), first) =>
                           (if first then () else TextIO.output (out, ",");
                            TextIO.output (out, "\"" ^ escaped field ^ "\":"); write out x; false))
                        true (fields tm));
     TextIO.output (out, "}"))
  else if stringSyntax.is_string_literal tm then
    TextIO.output (out, "\"" ^ escaped (stringSyntax.fromHOLstring tm) ^ "\"")
  else if numSyntax.is_numeral tm then
    TextIO.output (out, Arbnum.toString (numSyntax.dest_numeral tm))
  else if wordsSyntax.is_n2w tm andalso numSyntax.is_numeral (rand tm) then
    TextIO.output (out, Arbnum.toString (numSyntax.dest_numeral (rand tm)))
  else if Teq tm then TextIO.output (out, "true")
  else if Feq tm then TextIO.output (out, "false")
  else if listSyntax.is_list tm then
    (TextIO.output (out, "[");
     ignore (List.foldl (fn (x, first) => (if first then () else TextIO.output (out, ",");
                                           write out x; false))
                        true (fst (listSyntax.dest_list tm)));
     TextIO.output (out, "]"))
  else
    let
      val (f, args) = strip_comb tm
      val {Name, Thy, ...} = dest_thy_const f
        handle HOL_ERR _ => raise ERR "write" ("not a constructor term: " ^ term_to_string f)
    in
      if (Name = "strlit" orelse Name = "implode") andalso length args = 1 then write out (hd args)
      else
        (TextIO.output (out, "[\"" ^ escaped (Thy ^ "$" ^ Name) ^ "\"");
         List.app (fn x => (TextIO.output (out, ","); write out x)) args;
         TextIO.output (out, "]"))
    end

(* What the parser gives: the theorem has to be the equation of `parse`, the parser applied to the
   text, with no hypothesis, and rest on no oracle but the theories it was evaluated from. *)
fun given parse th =
  let
    val _ = null (hyp th) andalso aconv (lhs (concl th)) parse
      orelse raise ERR "show" "not the parser's equation for the text"
    val tag = Thm.tag th
    val _ = Tag.isEmpty tag orelse Tag.isDisk tag orelse raise ERR "show" "the theorem rests on an oracle"
  in
    rhs (concl th)
  end

(* The tree of the theorem into `path`; the parse has to have succeeded. *)
fun show path parse th =
  let
    val r = given parse th
    val _ = sumSyntax.is_inl r orelse raise ERR "show" "the parser refused the program"
    val out = TextIO.openOut path
  in
    write out (sumSyntax.dest_inl r |> fst);
    TextIO.output (out, "\n");
    TextIO.closeOut out
  end

(* The trees of several equations into `path`, as a JSON list, `null` for a text refused. *)
fun showEach path pairs =
  let
    val rs = map (fn (parse, th) => given parse th) pairs
    val out = TextIO.openOut path
    fun one r =
      if sumSyntax.is_inl r then write out (sumSyntax.dest_inl r |> fst)
      else if sumSyntax.is_inr r then TextIO.output (out, "null")
      else raise ERR "showEach" "neither a tree nor a refusal"
  in
    TextIO.output (out, "[");
    ignore (List.foldl (fn (r, first) => (if first then () else TextIO.output (out, ","); one r; false))
                       true rs);
    TextIO.output (out, "]\n");
    TextIO.closeOut out
  end

end
