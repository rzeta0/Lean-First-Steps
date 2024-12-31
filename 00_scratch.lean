import Mathlib.Tactic

--import LeanFirstSteps

---

lemma Nat.le_or_succ_le' (a b: ℕ): a ≤ b ∨ b + 1 ≤ a := by
  have h : a ≤ b ∨ b < a := le_or_lt a b
  rw [← Nat.succ_le] at h
  exact h

---

lemma Nat.le_or_succ_le (a b: ℕ): a ≤ b ∨ b + 1 ≤ a := by
  rw [Nat.succ_le]
  exact le_or_lt a b

---

def Sq: ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 * n + Sq n

#eval Sq 5

example {n: ℕ} : Sq n = n^2 := by
  induction n with
  | zero =>
    calc
      Sq 0 = 0 := by rw [Sq]
      _ = 0^2 := by norm_num
  | succ n ih =>
    calc
      Sq (n + 1) = 1 + 2 * n + Sq n := by rw [Sq]
      _ = 1 + 2 * n + n^2 := by rw [ih]
      _ = (n + 1)^2 := by ring

---

example {n : ℕ} : 3^n ≥ n + 1 := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    calc
      3^(n + 1) = 3 * 3^n := by ring
      _ ≥ 3 * (n + 1) := by rel [ih]
      _ = n + 1 + n + n + 1 + 1 := by ring
      _ ≥ (n + 1) + 1 := by norm_num
