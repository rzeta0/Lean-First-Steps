-- 01 - First Proof by Calculation

import Mathlib.Tactic

example {a: ℕ} (h1: a = 4) : a > 1 := by linarith

-- second?

example {x y : ℝ} (h1 : y = x + 4) (h2 : x = 3) : y = 7 :=
  calc
    y = x + 4 := by rw [h1]
    _ = 3 + 4 := by rw [h2]
    _ = 7 := by norm_num
