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

def T : ℕ → ℚ
  | 0 => 0
  | n + 1 => T n + (n + 1)

#eval T 4

example (n : ℕ) : T n = n * (n + 1) / 2 := by
  induction n with
  | zero =>
    calc T 0 = 0 := by rw [T]
      _ = 0 * (0 + 1) / 2 := by norm_num
  | succ n ih =>
    push_cast
    calc
      T (n + 1) = T n + (n + 1) := by rw [T]
      _ = n * (n + 1) / 2 + (n + 1) := by rw [ih]
      _ = (n + 1) * (n + 1 + 1) / 2 := by ring

---

def f : ℕ → ℤ
  | 0 => 1
  | n + 1 => -1 * f n

#eval f 3

example {n: ℕ} : f n = (-1)^n := by
  induction n with
  | zero =>
    calc
      f 0 = 1 := by rw [f]
      _ = (-1)^0 := by norm_num
  | succ n ih =>
    calc
      f (n + 1) = (-1) * f n := by rw [f]
      _ = (-1) * (-1)^n := by rw [ih]
      _ = (-1)^(n+1) := by ring

--
