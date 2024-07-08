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

example {x y : ℝ} (h1 : y = x^2 - 9) (h2 : x = -3) : y = 0 :=
  calc
    y = x^2 - 9 := by rw [h1]
    _ = (-3)^2 - 9 := by rw [h2]
    _ = 0 := by norm_num


-- 03 - Symbols, No Numbers
-- Write a Lean program to prove that z = x given z = y and y = x, where x,y,z ∈ ℝ.

example {x y z: ℝ} (h1 : z = y) (h2: y = x) : z = x :=
  calc
    z = y := by rw [h1]
    _ = x := by rw [h2]


-- 04 - Simple Algebra
-- Write a Lean program to prove (a+b)^2 = a^2 + b^2 if we know ab = 0, where a,b ∈ ℤ.

example {a b : ℤ} : (a - b) * (a + b) = a^2 - b^2 :=
  calc
    (a - b) * (a + b) = a^2 - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring


-- 05 - Inequalities
-- Write a Lean program to prove a < c if we know a < b and b ≤ c, where a,b,c ∈ ℕ.
example {a b c : ℕ} (h1: a < b) (h2: b ≤ c) : a < c :=
  calc
    a < b := by rel [h1]
    _ ≤ c := by rel [h2]
