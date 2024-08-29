-- 07 - Proof by Cases

import Mathlib.Tactic

example {x : ℤ} (h : x = 3 ∨ x = -3) : x^2 = 9 := by
  obtain ha | hb := h
  · calc
    x^2 = (3)^2 := by rw [ha]
    _ = 9 := by norm_num
  · calc
    x^2 = (-3)^2 := by rw [hb]
    _ = 9 := by norm_num
