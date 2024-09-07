-- 08 - Existence proof

import Mathlib.Tactic

example : ∃ x: ℕ , x^2 + 1 = 10 := by
  use 3
  calc
    3^2+ 1  = 10 := by norm_num

-- more concise
example : ∃ x: ℕ , x^2 + 1 = 10 := by
  use 3
  norm_num
