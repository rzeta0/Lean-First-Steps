-- 11 - Existence proof

import Mathlib.Tactic

example : ∃ n: ℕ, n^2 + 1 = 10 := by
  use 3
  calc
    3^2 + 1 = 10 := by norm_num

-- more concise
example : ∃ n: ℕ, n^2 + 1 = 10 := by
  use 3
  norm_num
