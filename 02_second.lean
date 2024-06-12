-- 02 - Simultaneous Equations with re-writing

import Mathlib.Tactic

example {x y : ℝ} (h1 : y - 2 = 2) (h2: y + x = 6) : x = 2 :=
  calc
    x = y + x - y := by ring
    _ = 6 - y := by rw [h2]
    _ = 6 - (y - 2) -2 := by ring
    _ = 6 - (2) - 2 := by rw [h1]
    _ = 2 := by norm_num
