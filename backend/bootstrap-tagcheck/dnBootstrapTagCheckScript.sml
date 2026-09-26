(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(*
  Ask the prover what the bootstrapped compiler's machine code rests on.

  `cake.S` is written by the proof of `compiler64_compiled`: the theorem that evaluating the
  compiler on its own source gives that code. Holmake reports a cheat by printing a word and
  exiting successfully, so the log is read elsewhere; this reads the theorem, with the same
  criterion as the proof lane's tag check (`check_tag` in `misc/preamble.sml`): read back from a
  theory file, a theorem that was proved carries `DISK_THM` and nothing else. As there, the
  axiom list of a loaded theorem is always empty and says nothing; this is about oracles.

  It is built outside both pinned trees, so it is not part of what it judges.
*)
open HolKernel boolLib x64BootstrapTheory;

val _ = new_theory "dnBootstrapTagCheck";

val tag = Thm.tag compiler64_compiled;
val (oracles, _) = Tag.dest_tag tag;

val _ =
  if Tag.isEmpty tag orelse Tag.isDisk tag then
    print "DN BOOTSTRAP: compiler64_compiled carries no oracle\n"
  else
    raise Fail ("DN BOOTSTRAP: compiler64_compiled depends on " ^
                String.concatWith ", " (List.filter (fn s => s <> "DISK_THM") oracles));

val _ = export_theory();
