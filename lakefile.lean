import Lake
open Lake DSL

package dn where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`maxRecDepth, 16384⟩,
                   ⟨`maxHeartbeats, 4000000⟩]

@[default_target]
lean_lib DN where
  srcDir := "lean"
  globs := #[.submodules `DN]

lean_exe «dn-compiler» where
  srcDir := "lean"
  root := `DN.Compiler.Main
