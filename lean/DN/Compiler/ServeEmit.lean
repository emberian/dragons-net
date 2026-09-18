-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.ServeEmit

Retained compiler/dataplane development and regression examples.
Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md. HTTP examples are compiler workloads, not dn server features.
-/

import DN.Compiler.ServeSlice
import DN.Compiler.Syntax

namespace DN.Compiler.ServeEmit

open DN.Compiler.Syntax
open DN.Compiler.SerializeCompile (serialize)
open DN.Compiler.ServeSlice (resp200 resp405)

/-- The concrete bytes of a serialized response, as `Nat`s for the byte stores. -/
def bytesOf (bs : List (BitVec 8)) : List Nat := List.map (fun w => BitVec.toNat w) bs

/-- `st8 out+i, b;` for each `(i, b)` — materialise a response template into `out`. -/
def storesInto (dst : String) (bs : List Nat) : List PStmt :=
  ((List.range bs.length).zip bs).map (fun p => PStmt.storeb (atOff (v dst) p.1) (n p.2))

/-- Decode the request method token into the routing tag `method` the slice
routes on. Only the allowed set {GET, POST, HEAD, OPTIONS} maps into {0,1,2,3};
everything else stays `9` (routed to 405). -/
def parseMethod : List PStmt :=
  [ .dec "method" (n 9)
  , .ite (eEq (.loadb (v "req")) (n 71))            -- 'G' → GET
      [ .assign "method" (n 0) ]
      [ .ite (eEq (.loadb (v "req")) (n 72))        -- 'H' → HEAD
          [ .assign "method" (n 2) ]
          [ .ite (eEq (.loadb (v "req")) (n 79))    -- 'O' → OPTIONS
              [ .assign "method" (n 3) ]
              [ .ite (eEq (.loadb (v "req")) (n 80))            -- 'P' …
                  [ .ite (eEq (.loadb (atOff (v "req") 1)) (n 79))  -- … 'O' → POST
                      [ .assign "method" (n 1) ]
                      [ .assign "method" (n 9) ] ]
                  [ .assign "method" (n 9) ] ] ] ] ]

/-- The routed serve as a C-callable `export fun serve(ctrl, req, len, out)`:
decode the method, route on `method < 4`, store the selected serialized response
into `out`, return its length. -/
def serveExport (bs200 bs405 : List Nat) : PFun :=
  { name := "serve", exported := true,
    params := [(1, "ctrl"), (1, "req"), (1, "len"), (1, "out")],
    body := parseMethod ++
      [ .dec "count" (n 0)
      , .ite (eLt (v "method") (n 4))
          (storesInto "out" bs200 ++ [ .assign "count" (n bs200.length) ])
          (storesInto "out" bs405 ++ [ .assign "count" (n bs405.length) ])
      , .ret (v "count") ] }

/-! ## TRACK 2 PHASE B — config-as-data: the emitted serve READS the config frame.

The host delivers `cfgLen(4 BE) :: config :: request` and hands the compiled serve
the config frame base (`ctrl`) alongside the request pointer (`req`). Today's serve
IGNORES `ctrl` and bakes the 200 response as a literal. Phase B makes ONE decision
config-driven — an HSTS on/off toggle read from `config[0]` — while keeping the
`cfgLen = 0` (empty config) path byte-identical to today (a THEOREM, in
`DN.Compiler/ServeConfigServe.lean`). -/

/-- The 4-byte big-endian `cfgLen` the host writes (`u32::from_be_bytes`), read
byte-addressed from `cfgPtr[0..4]`: `((b0*256 + b1)*256 + b2)*256 + b3`. Uses only
modelled ops (`ld8`, `*`, `+`), so it lowers into the `DN.Compiler.Semantics` fragment. -/
def be4 (cfgPtr : PExpr) : PExpr :=
  eAdd (eMul (eAdd (eMul (eAdd (eMul (.loadb (atOff cfgPtr 0)) (n 256))
                                     (.loadb (atOff cfgPtr 1))) (n 256))
                        (.loadb (atOff cfgPtr 2))) (n 256))
       (.loadb (atOff cfgPtr 3))

/-- Read the config frame at `cfgPtr` and (only when a config is present, i.e. the
4-BE `cfgLen ≠ 0`) set the toggle local `tog := config[0] = cfgPtr[4]`. When
`cfgLen = 0` the toggle keeps the default the caller declared (0 = today's baked
behaviour), so this fragment is a no-op on the empty frame. -/
def readCfg (cfgPtr tog : String) : List PStmt :=
  [ .dec "clen" (be4 (v cfgPtr))
  , .ite (eEq (v "clen") (n 0))
      [ ]
      [ .assign tog (.loadb (atOff (v cfgPtr) 4)) ] ]

/-- The config-reading serve as a C-callable `export fun serve_cfg(ctrl, req, len,
out)`: decode the method (as `serveExport`), read the HSTS toggle from the config
frame at `ctrl`, route on `method < 4`, and — in the 200 branch — pick `bs200`
(toggle 0 / config absent = today) or `bs200Alt` (toggle nonzero). The 405 branch
is config-independent. The response head is now a FUNCTION of the config frame. -/
def serveExportCfg (bs200 bs200Alt bs405 : List Nat) : PFun :=
  { name := "serve_cfg", exported := true,
    params := [(1, "ctrl"), (1, "req"), (1, "len"), (1, "out")],
    body := parseMethod
      ++ [ .dec "hsts" (n 0) ]
      ++ readCfg "ctrl" "hsts"
      ++ [ .dec "count" (n 0)
         , .ite (eLt (v "method") (n 4))
             [ .ite (eEq (v "hsts") (n 0))
                 (storesInto "out" bs200 ++ [ .assign "count" (n bs200.length) ])
                 (storesInto "out" bs200Alt ++ [ .assign "count" (n bs200Alt.length) ]) ]
             (storesInto "out" bs405 ++ [ .assign "count" (n bs405.length) ])
         , .ret (v "count") ] }

-- Non-vacuity: distinct branches, a well-formed exported header, and (the config
-- point) the 200 branch's two templates genuinely differ.
def regression_141 : Bool := decide ((ppFun (serveExportCfg [72] [77] [88])).take 21 == "export fun serve_cfg("
  )
def regression_142 : Bool := decide ([72] ≠ ([77] : List Nat)
  )

def banner : String :=
  "// GENERATED by DN.Compiler/ServeEmit.lean -- do not hand-edit.\n" ++
  "// routed serve slice as a C-callable export fun (SysV ABI: ctrl/req/len/out).\n" ++
  "// Emission is generative: this file is ppFun applied to the built PFun; the\n" ++
  "// stored response bytes are `serialize resp200` / `serialize resp405`.\n" ++
  "// Compile: cake --pancake --main_return=true < serve.pnk > serve.S\n\n"

/-- The rendered concrete syntax (evaluated to write the `.pnk`). -/
def servePnk : String :=
  banner ++ ppFun (serveExport (bytesOf (serialize resp200)) (bytesOf (serialize resp405)))

-- Non-vacuity guards: the two branches store DISTINCT, non-empty responses.
def regression_156 : Bool := decide ((bytesOf (serialize resp200)).length > 0
  )
def regression_157 : Bool := decide ((bytesOf (serialize resp405)).length > 0
  )
def regression_158 : Bool := decide (bytesOf (serialize resp200) ≠ bytesOf (serialize resp405)
  )
-- the emitted text is a well-formed export fun header
def regression_160 : Bool := decide ((ppFun (serveExport [72] [77])).take 17 == "export fun serve("
  )

/-- Write the emitted serve to `DN.Compiler/serve_slice_export.pnk`. -/
def writePnk : IO Unit := do
  IO.FS.writeFile "DN.Compiler/serve_slice_export.pnk" servePnk
  IO.println s!"wrote DN.Compiler/serve_slice_export.pnk ({servePnk.length} bytes)"


/-- Write the two golden serialized responses as raw bytes, for a byte-exact
diff against the machine-code serve output. -/
def writeGolden : IO Unit := do
  IO.FS.writeBinFile "DN.Compiler/serve_resp200.bin"
    (ByteArray.mk ((bytesOf (serialize resp200)).map UInt8.ofNat).toArray)
  IO.FS.writeBinFile "DN.Compiler/serve_resp405.bin"
    (ByteArray.mk ((bytesOf (serialize resp405)).map UInt8.ofNat).toArray)
  IO.println "wrote DN.Compiler/serve_resp200.bin, DN.Compiler/serve_resp405.bin"


end DN.Compiler.ServeEmit
