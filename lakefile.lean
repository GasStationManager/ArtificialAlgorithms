import Lake
open Lake DSL

package "ArtificialAlgorithms" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ git "v4.21.0"

@[default_target]
lean_lib «ArtificialAlgorithms» where
  -- add any library configuration options here
