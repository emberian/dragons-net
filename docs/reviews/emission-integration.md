# Emission and integration review

Review findings describe the inspected baseline, read at revision `94785d2`; line numbers are from that revision and the files have moved since. CakeML references are to the revision pinned in `backend/lock.json`. See [triage and current disposition](README.md) for fixes applied during this review and unresolved obligations.

Scope: `Syntax`, `Checked`, `Lower`, `Abi`, `Kernels`, and `Baseline`, with selective review of the inherited structure, serialization, stage, and serve modules. This review was read-only except for this report. I did not run a shared Lake build. A scratch `lake env lean` evaluation was used for the first reproducer. The parser analysis is based on the pinned source in `.deps/cakeml/pancake/parser`; the lead reviewer independently confirmed that the generated `ld8 ld8 p` source is rejected by the pinned CakeML executable on the Linux native host.

## Findings

### P1: `Checked.emit` accepts nested loads that `ppExpr` prints outside the Pancake grammar

`Checked.expression` accepts a load whose address is any recursively accepted expression (`lean/DN/Compiler/Checked.lean:22-28`). `Syntax.wrapAtom`, however, parenthesizes only a binary expression (`lean/DN/Compiler/Syntax.lean:88-92`), so nested loads are printed without parentheses (`lean/DN/Compiler/Syntax.lean:102-103`).

Reproducer:

```lean
#eval DN.Compiler.Checked.emit
  { name := "nested", exported := true, params := [(1, "p")],
    body := [.ret (.loadb (.loadb (.var "p")))] }
```

This evaluates to `Except.ok` with:

```pancake
export fun nested(1 p) {
  return ld8 ld8 p;
}
```

The pinned grammar makes `ld8` consume `ELoad32NT` (`.deps/cakeml/pancake/parser/panPEGScript.sml:290-292`), whose descendants do not accept a leading `ld8`; a parenthesized expression is accepted at `EBaseNT` (`panPEGScript.sml:332-344`). The analogous problem exists for `loadw`/`loadb` combinations. Thus the advertised checked emission boundary can return success for source the real parser should reject. The current differential family contains no loads (`lean/DN/Compiler/Baseline.lean:34-38`), while kernel memory tests use only arithmetic addresses, so the gap is invisible to the baseline.

Focused fix: make the load-address printer parenthesize `.loadw` and `.loadb` children as well as `.binop` children, or reject nested loads until that printer contract is established. Add a matrix covering `loadb(loadb p)`, `loadb(loadw 1 p)`, `loadw 1 (loadb p)`, and `loadw 1 (loadw 1 p)` through `Checked.emit` and the pinned CakeML parser/native lane. Compare the parsed/model result on valid memory, rather than checking only emitted string prefixes.

### P1 integration blocker if exposed: the inherited exported serve ignores request length and can fault on empty or one-byte input

`serveExport` exposes `(ctrl, req, len, out)`, but its body never reads `len` (`lean/DN/Compiler/ServeEmit.lean:52-67`). `parseMethod` immediately loads `req[0]`, and on a leading `P` loads `req[1]` (`ServeEmit.lean:32-50`). `serveExportCfg` repeats the same decoder (`ServeEmit.lean:100-120`). An empty request therefore attempts an invalid load; a one-byte `P` request attempts a second invalid load. In the Lean semantics, a failed load yields `none`, so the function does not produce its documented 405 response.

These are inherited research fixtures emitted directly with `ppFun`, not active CLI exports through `Checked.emit`. The issue is therefore a containment/integration blocker if a host exposes them, distinct from the active checked-emission defect above.

The capstone theorems do not cover this boundary. They assume the requested byte load already succeeds (`lean/DN/Compiler/ServeExportServes.lean:318-325` and `427-434`), and the 405 witness is an addressable `'X'`, which avoids `req[1]`. The executable regressions check serialized lengths and branch distinction, not truncated input (`ServeExportServes.lean:549-557`). This is an assumption-shaped coverage gap around the exported pointer/length ABI.

Focused fix: branch on a nonnegative/in-range `len` before every request load: require `len >= 1` for `req[0]` and `len >= 2` before `req[1]`, with an explicit error response/status for truncation. Add model cases for `len = 0`, `len = 1` with byte `P`, and a protected-page native test placing `req` at the allocation boundary. State whether `len` is signed-range restricted, as in the maintained kernels.

### P1 integration blocker if exposed: the inherited serve ABI has no output capacity, but writes 164 or 227 bytes unconditionally

`serveExport` has an output pointer but no output length/capacity parameter (`lean/DN/Compiler/ServeEmit.lean:52-62`). Once it chooses a branch, `storesInto` emits one `st8` per response byte (`ServeEmit.lean:28-30`, `63-67`). The concrete inherited responses are 164 and 227 bytes (`lean/DN/Compiler/ServeExportServes.lean:549-555`). The same flaw applies to the configurable serve at `ServeEmit.lean:100-120`.

The proofs assume addressability for every selected output byte (`ServeExportServes.lean:323-325` and `432-434`). That is a valid conditional model theorem, but it supplies no runtime enforcement and the four-argument ABI has no way to express the obligation. Consequently a caller that supplies a smaller output allocation crosses the native memory boundary before receiving the returned length.

As above, this is an inherited, directly printed fixture rather than an active CLI export. Its caller preconditions must remain explicit until a capacity-carrying ABI and native boundary tests exist.

Focused fix: redesign the export to include `outCap` (which likely requires an ABI decision because the current checked profile caps functions at four parameters at `lean/DN/Compiler/Checked.lean:45-53`), reject negative-as-signed values, and test `required <= outCap` without overflow before stores. Alternatively pass a control structure containing pointer/capacity/result slots. Add protected-page native tests at capacities 0, 163, 164, 226, and 227, and theorem branches showing rejection leaves output unchanged.

### P2: the claimed method-token decoder routes arbitrary prefixes as valid methods

The implementation accepts any input beginning with `G`, `H`, or `O`, and any input beginning with `PO` (`lean/DN/Compiler/ServeEmit.lean:32-50`). Examples such as `GARBAGE`, `H`, `OOPS`, and `PONG` take the 200 branch. Neither `len` nor a delimiter is consulted. The containment comment now describes this as prefix routing rather than token parsing. `serveExport_serves_get_real` correspondingly requires only that the first byte be `G` (`lean/DN/Compiler/ServeExportServes.lean:509-525`), so the theorem and implementation are circular with respect to full token classification rather than an independent parser check.

Focused fix: either rename and document this as a first-byte compiler workload, or compare every byte of each token plus the following delimiter under length guards. Test near misses and prefixes (`G`, `GETX`, `P`, `PO`, `PONG`, `HEADX`, `OPTIONSX`) against an independent reference decoder.

### P2: the config-reading export trusts an unbounded embedded length while lacking a buffer-length argument

`readCfg` always reads the four-byte length prefix and reads `ctrl[4]` whenever that value is merely nonzero (`lean/DN/Compiler/ServeEmit.lean:78-98`). `serveExportCfg` receives no control-buffer allocation length (`ServeEmit.lean:100-120`). A truncated prefix faults during `be4`; a four-byte frame declaring any nonzero length faults at byte four. It also does not ensure the declared length is at least one before consuming the toggle or is bounded by an allocation.

Current regressions only inspect the emitted header and assert that two constant templates differ (`ServeEmit.lean:122-127`); they never execute malformed/truncated frames.

Focused fix: include the actual control-buffer length in the ABI/control structure, establish `actual >= 4`, decode the prefix, and require `declared <= actual - 4`; require `declared >= 1` before loading the toggle. Cover actual lengths 0 through 5 and declared lengths 0, 1, and oversized values in both model and protected-memory native tests.

## Lower-priority integration observations

* `Abi.emitWord` appends an output parameter (`lean/DN/Compiler/Abi.lean:22-27`) after `Checked.emit` has accepted up to four parameters (`Checked.lean:45-53`). It therefore cannot adapt a four-parameter value-returning function: the transformed function has five parameters and is safely rejected. This is a documented native-profile limitation, not a correctness bug. A clearer early error saying the input limit for `emitWord` is three would improve usability; a future wider interface can instead use a control-structure ABI.
* The structure serializer's `storeLit` and `copyWhile` operate on abstract word slots at consecutive byte-valued addresses using word `Store`/`Load` (`lean/DN/Compiler/StructEmit.lean:46-58`, `lean/DN/Compiler/SerializeCompile.lean:203-221`). This is internally consistent with the transcription's word-addressed map, but it is not the byte-store path used by the real serve emitter. No printer/parser/native bridge was found for `respEmit`. Keep claims about those modules explicitly model-only; use `storeByte`/`loadByte` for a future concrete byte buffer and prove the representation correspondence.

## Coverage assessment

The maintained arithmetic baseline is broad for its selected operators, but it deliberately serializes loads as JSON `null` and does not generate memory expressions (`lean/DN/Compiler/Baseline.lean:34-38`). The native kernel tests exercise fixed, hand-shaped address expressions. This combination masks printer bugs in recursively composed memory expressions. The inherited serve proofs establish behavior only under successful input loads and fully addressable output regions, while the ABI omits the lengths needed to enforce those premises. The next emission tests should therefore generate bounded ASTs containing nested loads and should place exported pointers next to inaccessible pages so that ABI bounds are executable properties rather than caller-only assumptions.
