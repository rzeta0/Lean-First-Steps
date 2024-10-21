-- 14 - Using Lemmas: Multiplied Factors Equal Zero

import Mathlib.Tactic

example {a b : ℚ} (h: (a - 1) * (b - 2) = 0): a = 1 ∨ b = 2 := by
  rw [mul_eq_zero] at h
  obtain ha | hb := h
  · left
    calc
      a = a - 1 + 1 := by ring
      _ = 0 + 1 := by rw [ha]
      _ = 1 := by norm_num
  · right
    calc
      b = b - 2 + 2 := by ring
      _ = 0 + 2 := by rw [hb]
      _ = 2 := by norm_num

--

example {a b : ℚ} (h: (a - 1) * (b - 2) = 0): a = 1 ∨ b = 2 := by
  rw [mul_eq_zero] at h
  obtain ha | hb := h
  · left
    linarith
  · right
    linarith
