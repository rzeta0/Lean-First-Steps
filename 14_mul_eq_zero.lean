-- 14 - Using Lemmas: Multiplied Factors Equal Zero

import Mathlib.Tactic

example {p q : ℚ} (h: (p - 1) * (q - 2) = 0): p = 1 ∨ q = 2 := by
  rw [mul_eq_zero] at h
  obtain hp | hq := h
  · left
    linarith
  · right
    linarith
