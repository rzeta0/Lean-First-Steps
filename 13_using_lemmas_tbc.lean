-- 13 - Using Lemmas: TBC

import Mathlib.Tactic

example {n : ℕ} : n^2 ≠ 2 := by
  -- have h := le_or_succ_le n 1
  have h := le_or_lt n 1
  obtain ha | hb := h
  · apply ne_of_lt
    calc
      n^2 ≤ (1)^2 := by rel [ha]
      _ < 2 := by norm_num
  · apply ne_of_gt
    have h2 := Nat.succ_le_of_lt hb
    calc
      n^2 ≥ (2)^2 := by rel [h2]
      _ > 2 := by norm_num
