-- 07a - Conjunctive "and" Hypothesis

import Mathlib.Tactic

example {x y : ℤ} (h : x = 5 ∧ y = x + 3) : y = 8 := by
  obtain ⟨ ha , hb ⟩ := h
  calc
    y = x + 3 := by rw [hb]
    _ = (5) + 3 := by rw [ha]
    _ = 8 := by norm_num



-- 07b - Disjunctive Goal

example {x : ℤ} (h : x = -1) : x^2 = 1 ∨ x^2 = -1 := by
  left
  calc
    x^2 = (-1)^2 := by rw [h]
    _ = 1 := by norm_num

-- note: head and tail example


-- 07c - Conjunctive Goal

example {x : ℤ} (h : x = -1) : x^2 = 1 ∧ x^3 = -1 := by
  constructor
  · calc
      x^2 = (-1)^2 := by rw [h]
      _ = 1 := by norm_num
  · calc
      x^3 = (-1)^3 := by rw [h]
      _ = -1 := by norm_num
