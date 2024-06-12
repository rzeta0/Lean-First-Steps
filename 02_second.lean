-- 02 - Second Proof by Calculation

import Mathlib.Tactic

example {y a b : ℝ} (h1 : y = (a - b) * (a + b)) : y = a^2 - b^2 :=
  calc
    y = (a - b) * (a + b) := by rw [h1]
    _ = a^2 - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring
