-- SPDX-License-Identifier: AGPL-3.0-or-later
/-!
# DN.Compiler.SplitMix

SplitMix64. The generated-programs lane fills buffers with it in the model, in the independent
interpreter and in the host, so it is written out here rather than taken from a library.
-/

namespace DN.Compiler.SplitMix

def golden : UInt64 := 0x9E3779B97F4A7C15

def mix (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- Output `i` (from zero) of SplitMix64 started at `seed`. -/
def splitmix (seed : UInt64) (i : Nat) : UInt64 := mix (seed + golden * UInt64.ofNat (i + 1))

end DN.Compiler.SplitMix
