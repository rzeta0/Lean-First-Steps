-- 05 - Simple Inequality

import Mathlib.Tactic

example {a b : ℕ} (h1 : b = a^2) (h2: a ≥ 2) : b ≥ 4 :=
  calc
    b = a^2 := by rw [h1]
    _ ≥ (2)^2 := by rel [h2]
    _ = 4 := by norm_num


example {x y : ℤ} (h1 : y = (x-2)*(x+2)) (h2: x ≥ 0) : y ≥ -4 :=
  calc
    y = (x-2)*(x+2) := by rw [h1]
    _ ≥ (0-2)*(x+2) := by rel [h2]
    _ ≥ (0-2)*(0+2) := by rel [h2]
    _ = -4 := by norm_num


    example {a b c d : ℕ} (h1 : a > b) (h2: b = c) (h3: c ≥ d) : a ≥ d :=
  calc
    a > b := by rel [h1]
    _ = c := by rw [h2]
    _ ≥ d := by rel [h3]
