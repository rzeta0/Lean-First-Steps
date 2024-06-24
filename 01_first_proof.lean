-- 01 - First Proof

import Mathlib.Tactic

example {a : ℕ} (h1: a = 4) : a > 1 :=
  calc
    a = 4 := by rw [h1]
    _ > 1 := by norm_num
