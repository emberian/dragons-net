(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(*
  What dnModel's dn_sem ends in on a case of the state corpus, printed the way dn-compiler
  dump-states prints the Lean model's answer, with dnShow's helpers.
*)
Theory dnModelShow
Ancestors
  dnModel dnShow
Libs
  wordsLib

Definition dn_mres_def:
  dn_mres (NONE : dn_result option) = "none" /\
  dn_mres (SOME RError) = "error" /\
  dn_mres (SOME RTimeout) = "timeout" /\
  dn_mres (SOME RBreak) = "break" /\
  dn_mres (SOME RContinue) = "continue" /\
  dn_mres (SOME (RReturn w)) = "return:" ++ dn_word w /\
  dn_mres (SOME (RFinalFFI e)) =
    "final:" ++ (if e.fname = "" then "_" else e.fname) ++ ":" ++ dn_hexs e.fconf ++ ":" ++
    dn_hexs e.farray ++ ":" ++ (case e.foutcome of OFailed => "failed" | ODiverged => "diverged")
End

Definition dn_model_show_def:
  dn_model_show (names : string list) (dom : word64 list)
                ((r, s) : dn_result option # (num # string list) dn_state) =
    "RESULT " ++ dn_mres r ++
    "\nFLOCALS " ++
      dn_join "," (MAP (\n. n ++ "=" ++ (case s.locals n of SOME w => dn_word w | NONE => "")) names) ++
    "\nFMEM " ++ dn_join "," (MAP (\a. dn_word a ++ "=" ++ dn_word (s.memory a)) dom) ++
    "\nFCALLS " ++ num_to_dec_string (FST s.ffi) ++
    "\nFTRACE " ++ dn_join ";" (SND s.ffi) ++
    "\nFCLOCK " ++ num_to_dec_string s.clock ++
    "\nFBASE " ++ dn_word s.baseAddr
End

Definition dn_model_written_def:
  dn_model_written (dom : word64 list) (m : word64 -> word64) =
    "WRESULT " ++ dn_join "," (MAP (\a. dn_word a ++ "=" ++ dn_word (m a)) dom)
End
