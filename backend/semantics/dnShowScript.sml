(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(*
  What panSem's evaluate ends in, printed the way dn-compiler dump-states prints the Lean
  model's answer: the result constructor, the named locals, the words of the memory domain, the
  call count and the trace of the oracle, the clock and the base address. Anything the corpus
  cannot reach (a value other than a word, an event on shared memory, an exception) prints as
  something no Lean answer is, so a case that reaches it disagrees.
*)
open HolKernel boolLib bossLib panLangTheory panSemTheory ffiTheory ASCIInumbersTheory;

val _ = new_theory "dnShow";

Definition dn_hexd_def:
  dn_hexd (n : num) = if n < 10 then CHR (48 + n) else CHR (87 + n)
End

Definition dn_hexs_def:
  dn_hexs (bs : word8 list) =
    if NULL bs then "-" else FLAT (MAP (\w. [dn_hexd (w2n w DIV 16); dn_hexd (w2n w MOD 16)]) bs)
End

Definition dn_join_def:
  dn_join (sep : string) [] = "" /\
  dn_join sep [x] = x /\
  dn_join sep (x :: y :: xs) = x ++ sep ++ dn_join sep (y :: xs)
End

Definition dn_word_def:
  dn_word (w : word64) = num_to_dec_string (w2n w)
End

Definition dn_name_def:
  dn_name (n : mlstring) = if n = strlit "" then "_" else explode n
End

Definition dn_res_def:
  dn_res (NONE : (64 result) option) = "none" /\
  dn_res (SOME Error) = "error" /\
  dn_res (SOME TimeOut) = "timeout" /\
  dn_res (SOME Break) = "break" /\
  dn_res (SOME Continue) = "continue" /\
  dn_res (SOME (Return (Val (Word w)))) = "return:" ++ dn_word w /\
  dn_res (SOME (FinalFFI (Final_event (ExtCall n) conf bs out))) =
    "final:" ++ dn_name n ++ ":" ++ dn_hexs conf ++ ":" ++ dn_hexs bs ++ ":" ++
    (if out = FFI_failed then "failed" else "diverged") /\
  dn_res _ = "unreachable"
End

Definition dn_val_def:
  dn_val (SOME (Val (Word (w : word64)))) = dn_word w /\
  dn_val (NONE : (64 v) option) = "" /\
  dn_val _ = "unreachable"
End

Definition dn_event_def:
  dn_event (IO_event (ExtCall n) conf ps) =
    explode n ++ ":" ++ dn_hexs conf ++ ":" ++ dn_hexs (MAP FST ps) /\
  dn_event _ = "unreachable"
End

Definition dn_mem_def:
  dn_mem (dom : word64 list) m =
    dn_join "," (MAP (\a. dn_word a ++ "=" ++ (case m a of Word v => dn_word v | _ => "unreachable")) dom)
End

Definition dn_show_def:
  dn_show (names : string list) dom ((r, s) : (64 result) option # (64, num) panSem$state) =
    "RESULT " ++ dn_res r ++
    "\nFLOCALS " ++ dn_join "," (MAP (\n. n ++ "=" ++ dn_val (FLOOKUP s.locals (implode n))) names) ++
    "\nFMEM " ++ dn_mem dom s.memory ++
    "\nFCALLS " ++ num_to_dec_string s.ffi.ffi_state ++
    "\nFTRACE " ++ dn_join ";" (MAP dn_event s.ffi.io_events) ++
    "\nFCLOCK " ++ num_to_dec_string s.clock ++
    "\nFBASE " ++ dn_word s.base_addr
End

Definition dn_written_def:
  dn_written dom m = "WRESULT " ++ dn_mem dom m
End

val _ = export_theory ();
