-- 15 - Using Lemmas: Multiplied Factors Equal Zero

import Mathlib.Tactic

example {p q : ℚ} (h : (p - 1) * (q - 2) = 0) : p = 1 ∨ q = 2 := by
  apply mul_eq_zero.mp at h
  obtain hp | hq := h
  · left
    linarith
  · right
    linarith
