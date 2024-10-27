-- 05 - Simple Inequality

import Mathlib.Tactic

example {a b : ℕ} (h1 : b = a^2) (h2 : a ≥ 2) : b ≥ 4 := by
  calc
    b = a^2 := by rw [h1]
    _ ≥ (2)^2 := by rel [h2]
    _ = 4 := by norm_num
