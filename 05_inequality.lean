-- 05 - Simple Inequality

import Mathlib.Tactic

example {a : ℕ} (h1 : a = 2) : a^2 ≥ 4 :=
  calc
    a^2 = 2^2 := by rw [h1]
    _ = 4 := by ring
    _ ≥ 4 := by norm_num
