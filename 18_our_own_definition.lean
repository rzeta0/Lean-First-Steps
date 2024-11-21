-- 18 - Our Own Definition

import Mathlib.Tactic

def Triangle (a : ℕ) : Prop := ∃ n, 2 * a = n * (n + 1)

example : Triangle 10 := by
  dsimp [Triangle]
  use 4
