-- 16 - Writing Our Own Lemma

import Mathlib.Tactic

lemma Nat.le_or_succ_le (a b: ℕ): a ≤ b ∨ b + 1 ≤ a := by
  rw [Nat.succ_le]
  exact le_or_lt a b

example {a : ℕ} :  a ≤ 2 ∨ 3 ≤ a  := by
  apply Nat.le_or_succ_le a 2
