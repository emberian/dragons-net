-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.News.RecoverCert
import DN.Compiler.AnalyzerCertSound

/-!
# DN.News.RecoverSafe

**Recovery's step never fails, whatever its caller does.** `RecoverProg.analysisMain` runs the
step in a loop, its area at `@base + analysisAt` and an external call between steps that may
write all of it; for every FFI oracle, every clock and every content of the heap, a run of it from
a state whose heap covers the area above the header never ends in `Fail` (`Entry.Fails`). The
safety analysis accepts it in the pieces of `DN.News.RecoverCert`, and
`DN.Compiler.AnalyzerCertSound` proves that a program a certificate accepts, its claims holding,
never fails. Recovery is to run in the session's `main`, whose theorem needs this of it.
-/

namespace DN.News.RecoverSafe

open DN.Compiler DN.Compiler.Analyzer DN.News.RecoverCert

variable {σ : Type}

/-- **Recovery's step never fails, whatever its caller does.** -/
theorem never_fails (o : Oracle σ) (s : PancakeState σ)
    (h : Covers (RecoverProg.analysisAt + RecoverProg.size) s.memaddrs s.baseAddr) :
    ¬ Entry.Fails o mainP s :=
  never_failsC o accepted claims_ok s h

/-- The premise holds of a heap of just the area, above the first page. -/
theorem covers_witness :
    Covers (RecoverProg.analysisAt + RecoverProg.size)
      (heapWords 4096 (RecoverProg.analysisAt + RecoverProg.size)) 4096 :=
  covers_heap _ (Nat.le_refl _) (by decide +kernel) (by decide +kernel)

end DN.News.RecoverSafe
