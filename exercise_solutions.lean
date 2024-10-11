-- Exercise Solutions

import Mathlib.Tactic

-- 01 - First Proof
-- The Lean program above proves a > 1 given a = 4. Change it to prove a < 10 given a = 4.

example {a: ℕ} (h1: a = 4) : a < 10 := by
  calc
    a = 4 := by rw [h1]
    _ < 10 := by norm_num


-- 02 - Simple Proof by Calculation
-- Write a Lean program to prove y = 0 given y = x^2 - 9 and x = -3, where x,y ∈ ℝ.

example {x y : ℝ} (h1 : y = x^2 - 9) (h2 : x = -3) : y = 0 := by
  calc
    y = x^2 - 9 := by rw [h1]
    _ = (-3)^2 - 9 := by rw [h2]
    _ = 0 := by norm_num


-- 03 - Symbols, No Numbers
-- Write a Lean program to prove that z = x given z = y and y = x, where x,y,z ∈ ℝ.

example {x y z: ℝ} (h1 : z = y) (h2: y = x) : z = x := by
  calc
    z = y := by rw [h1]
    _ = x := by rw [h2]


-- 04 - Simple Algebra
-- Write a Lean program to prove (a+b)^2 = a^2 + b^2 if we know ab = 0, where a,b ∈ ℤ.

example {a b : ℤ} : (a - b) * (a + b) = a^2 - b^2 := by
  calc
    (a - b) * (a + b) = a^2 - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring


-- 05 - Inequalities
-- Write a Lean program to prove a < c if we know a < b and b ≤ c, where a,b,c ∈ ℕ.
example {a b c : ℕ} (h1: a < b) (h2: b ≤ c) : a < c := by
  calc
    a < b := by rel [h1]
    _ ≤ c := by rel [h2]


-- 06 - Intermediate Result
-- Write a Lean program to prove a=2, given a = b + c, b - 1 = 0, and c + 1 = 2 where a,b,c ∈ ℤ.

example {a b : ℤ} (h1 : a = b + c) (h2: b - 1 = 0) (h3: c + 1 = 2) : a = 2 := by
  have h4: b = 1 := by linarith [h2]
  have h5: c = 1 := by linarith [h3]
  calc
    a = b + c := by rw [h1]
    _ = 1 + 1 := by rw [h4, h5]
    _ = 2 := by norm_num


-- 07 - Proof By Cases
-- Write a Lean program to prove x^2 - 3*x + 2 = 0, given (x = 1) ∨ (x = 2), where x ∈ ℝ.

example {x : ℝ} (h: x = 1 ∨ x = 2 ) : x^2 - 3*x + 2 = 0 := by
  obtain ha | hb := h
  · calc
    x^2 - 3*x + 2 = (1)^2 - 3*(1) + 2 := by rw [ha]
    _ = 0 := by norm_num
  · calc
    x^2 - 3*x + 2 = (2)^2 - 3*(2) + 2 := by rw [hb]
    _ = 0 := by norm_num


-- 08 - Conjunctive "and" Hypothesis
-- Write a Lean program to show that y≥8, given (x ≥ 5) ∧ (y = x+3), where x,y ∈ ℤ.

example {x y : ℤ} (h : x ≥ 5 ∧ y = x + 3) : y ≥ 8 := by
  obtain ⟨ ha , hb ⟩ := h
  calc
    y = x + 3 := by rw [hb]
    _ ≥ (5) + 3 := by rel [ha]
    _ = 8 := by norm_num


-- 09 - Disjunctive "or" Goal
-- Write a Lean program to show that (x = 1) ∨ (x^2 = 1) ∨ (x^3 = 1) given integer x = -1.

example {x : ℤ} (h : x = -1) : x = 1 ∨ x^2 = 1 ∨ x^3 = 1 := by
  right
  left
  calc
    x^2 = (-1)^2 := by rw [h]
    _ = 1 := by norm_num


-- 10 - Conjunctive "and" Goal
-- Write a Lean program to show that (x^3 = -1) ∧ (x^4 = 1) ∧ (x^5 = -1) given integer x = -1.

example {x : ℤ} (h : x = -1) : x^3 = -1 ∧ x^4 = 1 ∧ x^5 = -1:= by
  constructor
  · calc
      x^3 = (-1)^3 := by rw [h]
      _ = -1 := by norm_num
  · constructor
    · calc
        x^4 = (-1)^4 := by rw [h]
        _ = 1 := by norm_num
    · calc
        x^5 = (-1)^5 := by rw [h]
        _ = -1 := by norm_num


-- 11 - Existence
-- Write a Lean program to prove there exists a natural number larger than 5.

example : ∃ n : ℕ, n > 5 := by
  use 6
  calc
    6 > 5 := by norm_num

-- more concise version
example : ∃ n : ℕ, n > 5 := by
  use 6
  norm_num


-- 12 - Using Definitions: Odd & Even Numbers

example : Even (14: ℤ)  := by
  dsimp [Even]
  use 7
  norm_num


-- 13 - Using Lemmas: Not Equal from Less Than
-- Write a Lean program to prove n ≠ 5, given n > 5, for n ∈ ℕ

example {n : ℕ} (h: n > 5): n ≠ 5 := by
  apply ne_of_gt
  apply h
