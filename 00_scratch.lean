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

--


---
-- note the 2*a to avoid division by 2 with naturals
def Triangle (a : ℕ) : Prop := ∃ n, 2 * a = n * (n + 1)

example : Triangle 10 := by
  dsimp [Triangle]
  use 4

---

-- src https://www.shyamsundergupta.com/triangle.htm
example {t : ℕ} (h1: Triangle t) : Triangle (9*t + 1) := by
  dsimp [Triangle] at *
  obtain ⟨s, hs⟩ := h1
  use 3*s + 1
  calc
    2 * (9 * t + 1) = 9 * (2 * t) + 2 := by ring
    _ = 9 * (s * (s + 1)) + 2 := by rw [hs]
    _ = 9*s^2 + 9*s + 2 := by ring
    _ = ((3*s + 1)) * ((3*s + 1) + 1) := by ring

---

example {t: ℕ} (h1: Triangle t) : ∃ n, 8 * t + 1 = n^2 := by
  dsimp [Triangle] at *
  obtain ⟨s, hs⟩ := h1
  use 2*s + 1
  calc
    8*t + 1 = 4 * (2 * t) + 1 := by ring
    _ = 4 * (s*(s + 1)) + 1 := by rw [hs]
    _ = 4*s^2 +4*s + 1 := by ring
    _ = (2*s + 1)^2 := by ring

---

-- reductio ad absurdum

example {n : ℕ} (h: n = 5) : ¬ n = 1 := by
  intro hn
  have g :=
    calc
      5 = n := by rw [h]
      _ = 1 := by rw [hn]
  contradiction
  --linarith


----

example {n : ℕ} : 2^n ≥ n + 1 := by
  induction' n with k hk
  · -- base case
    norm_num
  · -- inductive step
    calc
      2^(k + 1) = 2 * 2^k := by ring
      _ ≥ 2 * (k + 1) := by rel [hk]
      _ = (k + 1) + 1 + k := by ring
      _ ≥ (k + 1) + 1 := by norm_num


example {n : ℕ} : 2^n ≥ n + 1 := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    calc
      2^(n + 1) = 2 * 2^n := by ring
      _ ≥ 2 * (n + 1) := by rel [ih]
      _ = (n + 1) + 1 + n := by ring
      _ ≥ (n + 1) + 1 := by norm_num


----

-- number
example {n : ℕ } : n + 1 ≥ n := by
  calc
    n + 1 ≥ n := by norm_num

-- non-negative variable
example {n m : ℕ } : n + m ≥ n := by
  calc
    n + m ≥ n := by norm_num

-- non-negative square
example {n m : ℤ } : n + m^2 ≥ n := by
  calc
    n + m^2 ≥ n := by nlinarith

---
