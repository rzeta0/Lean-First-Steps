-- 17 - Using Our Own Lemma

import Mathlib.Tactic

---

lemma Nat.le_or_succ_le (a b: ℕ): a ≤ b ∨ b + 1 ≤ a := by
  rw [Nat.add_one_le_iff]
  exact le_or_lt a b

---

example {n : ℕ} :  n^2 ≠ 7  := by
  have h := Nat.le_or_succ_le n 2
  obtain ha | hb := h
  · apply ne_of_lt
    calc
      n^2 ≤ 2^2 := by rel [ha]
      _ < 7 := by norm_num
  · apply ne_of_gt
    calc
      n^2 ≥ 3^2 := by rel [hb]
      _ > 7 := by norm_num
