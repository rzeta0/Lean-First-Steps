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
      _ = 2*(2*m^2 + m) := by ring
  · use 2*m^2 + 3*m + 1
    calc
      n^2 + n = (2*m + 1)^2 + (2*m + 1) := by rw [hb]
      _ = 2*(2*m^2 + 3*m + 1) := by ring

--

-- alternative using Odd and Even
-- remember to do an Int version from Nat

example {n : ℤ} : Even (n^2 + n) := by
  have h: Even n ∨ Odd n := Int.even_or_odd n
  obtain ha | hb := h
  · dsimp [Odd, Even] at *
    obtain ⟨x, hx⟩ := ha
    use 2*x^2 + x
    calc
      n^2 + n = (x + x)^2 + (x + x) := by rw [hx]
      _ = (2*x^2 + x) + (2*x^2 + x) := by ring
  · dsimp [Odd, Even] at *
    obtain ⟨y, hy⟩ := hb
    use 2*y^2 + 3*y + 1
    calc
      n^2 + n = (2*y + 1)^2 + (2*y + 1) := by rw [hy]
      _ = (2*y^2 + 3*y + 1) + (2*y^2 + 3*y + 1) := by ring

-----

-- from leanprover zulip

example {n : ℤ} : Even (n^2 + n) := by
  have  g: n^2 = n * n := by ring
  rw [g]
  obtain ha | hb := Int.even_or_odd n
  · apply Even.add
    · apply Even.mul_left ha
    · apply ha
  · apply Odd.add_odd
    · apply Odd.mul hb hb
    · apply hb

-----

example {n : ℤ} : Even ( n*(n+1) ) := by
  obtain ha | hb := Int.even_or_odd n
  · apply Even.mul_right ha
  · have g1: ¬ Even n := Int.not_even_iff_odd.mpr hb
    have g2: Even (n+1) := Int.even_add_one.mpr g1
    apply Even.mul_left g2


---

example {n : ℤ} : Even ( n*(n+1) ) := by
  obtain ha | hb := Int.even_or_odd n
  · apply Even.mul_right ha
  · apply Even.mul_left
    --rw [Int.even_add_one,Int.not_even_iff_odd]
    rw [Int.even_add_one]
    rw [Int.not_even_iff_odd]
    apply hb

-----

example {n : ℤ } : Even (n*(n+1)) := by
  apply Int.even_mul_succ_self

-----


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
---

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

----

-- Is Square?

example {a : ℕ} (h: a = 9) : IsSquare a := by
  dsimp [IsSquare]
  use 3

example : IsSquare 9 := by
  dsimp [IsSquare]
  use 3

----

-- IsSquare.not_prime

example {a : ℕ} (h: a = 9) : ¬ Prime (a) := by
  have h1: IsSquare a := by
    dsimp [IsSquare]
    use 3
  apply IsSquare.not_prime h1

---

example : ¬ Nat.Prime (12) := by
  have g: 12 = 3*4 := by norm_num
  rw [g]
  have h1: 3 ≠ 1 := by norm_num
  have h2: 4 ≠ 1 := by norm_num
  apply Nat.not_prime_mul h1 h2

--
---


-- 13 - Lemma: Not Equal from Less Than
-- but applied to hypthesis

example {n : ℕ} (h : n < 5) : n ≠ 5 := by
  apply ne_of_lt at h
  exact h


---


example {p q : ℚ} (h : p = 1 ∨ q = 2) : (p - 1) * (q - 2) = 0:= by
