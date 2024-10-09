import Mathlib.Tactic

import LeanFirstSteps

---

example {n : ℕ} : ∃ k: ℕ, n^2 + n = 2*k := by
  have h : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := Nat.even_or_odd' n
  obtain ⟨m , hm⟩ := h
  obtain ha | hb := hm
  · use 2*m^2 + m
    calc
      n^2 + n = (2*m)^2 + (2*m) := by rw [ha]
      _ = 4*m^2 + 2*m := by ring
      _ = 2*(2*m^2 + m) := by ring
  · use 2*m^2 + 3*m + 1
    calc
      n^2 + n = (2*m + 1)^2 + (2*m + 1) := by rw [hb]
      _ = 4*m^2 + 4*m + 1 + 2*m + 1 := by ring
      _ = 2*(2*m^2 + 3*m + 1) := by ring

--


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

---

-- uses le_or_succ_le lemma
example {n : ℕ} : n^2 ≠ 2 := by
  have h := Nat.le_or_succ_le n 1
  obtain ha | hb := h
  · apply ne_of_lt
    calc
      n^2 ≤ (1)^2 := by rel [ha]
      _ < 2 := by norm_num
  · apply ne_of_gt
    calc
      n^2 ≥ (2)^2 := by rel [hb]
      _ > 2 := by norm_num

--

-- not_prime_pow

example {a : ℕ} (h: a = 9) : ¬ Prime (a) := by
  -- h1 : a = 3 ^ 2
  have h1 :=
    calc
      a = 9 := by rw [h]
      _ = 3^2 := by ring
  -- h2 : 2 ≠ 1
  have h2 : 2 ≠ 1 := by
    apply ne_of_gt
    norm_num
  rw [h1]
  apply not_prime_pow h2

---

-- IsSquare.not_prime

example {a : ℕ} (h: a = 9) : ¬ Prime (a) := by
  have h1: IsSquare a := by
    dsimp [IsSquare]
    use 3
  apply IsSquare.not_prime h1

---
