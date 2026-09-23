(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(*
  Ask the prover itself what the rebuilt compiler theorem rests on.

  Holmake reports a cheat by printing a word and exiting successfully, so the proof lane reads
  its output; this reads the theorem instead. An oracle in the tag means the theorem was
  accepted on someone's word, and `cheat` is one such oracle. A theorem read back from a theory
  file carries `DISK_THM` and nothing else, which is upstream's own criterion (`check_tag` in
  `misc/preamble.sml`) for a theorem that was proved rather than assumed.

  What this cannot see: a theory file keeps the oracles of a theorem but not its axiom nonces
  (`Tag.read_disk_tag` builds the tag with an empty axiom list), so the axiom list of a loaded
  theorem is always empty and says nothing. Upstream applies the same criterion in memory,
  where the axioms are still there; this one is about oracles.

  It is built outside both pinned trees, against the theory Holmake has just produced, so it is
  not part of what it judges.
*)
open HolKernel boolLib pan_to_targetProofTheory;

val _ = new_theory "dnTagCheck";

val theorem = pan_to_target_compile_semantics;
val tag = Thm.tag theorem;
val (oracles, _) = Tag.dest_tag tag;

val _ =
  if Tag.isEmpty tag orelse Tag.isDisk tag then
    print "DN BACKEND: pan_to_target_compile_semantics carries no oracle\n"
  else
    raise Fail ("DN BACKEND: pan_to_target_compile_semantics depends on " ^
                String.concatWith ", " (List.filter (fn s => s <> "DISK_THM") oracles));

val _ = export_theory();
