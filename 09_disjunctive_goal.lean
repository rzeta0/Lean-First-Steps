-- 09 - Disjunctive "or" Goal

import Mathlib.Tactic

example {x : ℤ} (h : x = -1) : x^2 = 1 ∨ x^3 = 1 := by
  left
  calc
    x^2 = (-1)^2 := by rw [h]
    _ = 1 := by norm_num

-- note: head and tail example
