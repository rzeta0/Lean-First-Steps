-- 20 - Contradictory Cases

import Mathlib.Tactic

example {x : ℝ} (h1 : (x + 3) * (x - 3) = 0) (h2 : ¬ x = 3) : x = - 3 := by
  rw [mul_eq_zero] at h1
  obtain ga | gb := h1
  · linarith
  · have gc: x = 3 := by linarith
    contradiction


example {x : ℝ} (h1 : (x + 3) * (x - 3) = 0) (h2 : x > 0) : x = 3 := by
  rw [mul_eq_zero] at h1
  obtain ga | gb := h1
  · have gx := by
      calc
        x = -3 := by linarith
        _ < 0 := by norm_num
    have gx2: ¬ x > 0 := by linarith [gx]
    contradiction
  · linarith

