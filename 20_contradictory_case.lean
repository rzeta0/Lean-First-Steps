-- 20 - Contradictory Cases

import Mathlib.Tactic

example {x : ℝ} (h1 : (x + 3) * (x - 3) = 0) (h2 : ¬ x = 3) : x = - 3 := by
  rw [mul_eq_zero] at h1
  obtain ga | gb := h1
  · linarith
  · have gc: x = 3 := by linarith
    contradiction
