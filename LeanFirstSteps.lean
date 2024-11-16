import Mathlib.Tactic

---

lemma Nat.le_or_succ_le (a b: ℕ): a ≤ b ∨ b + 1 ≤ a := by
  rw [Nat.add_one_le_iff]
  exact le_or_lt a b

example {c : ℕ} :  c ≤ 2 ∨ 3 ≤ c  := by
  exact Nat.le_or_succ_le c 2

---

lemma Int.even_of_odd_add_one {a: ℤ} (h: Odd a): Even (a + 1) := by
  have g1: ¬ Even a := Int.not_even_iff_odd.mpr h
  have g2: Even (a + 1) := Int.even_add_one.mpr g1
  apply g2

example (h: Odd (3 : ℤ)) : Even (4 : ℤ)  := by
  have g: (4 : ℤ) = 3 + 1 := by norm_num
  rw [g]
  apply Int.even_of_odd_add_one h

---
