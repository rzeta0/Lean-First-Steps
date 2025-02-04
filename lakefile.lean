import Lake
open Lake DSL

package «leantest» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"


-- lemmas used by this course
-- lean_lib LeanFirstSteps

@[default_target]
lean_lib «Leantest» where
  -- add any library configuration options here
