-- 05 - Simple Inequality

import Mathlib.Tactic

example {a : ℕ} (h1 : a = 2) : a^2 ≥ 4 :=
  calc
    a^2 = 2^2 := by rw [h1]
    _ = 4 := by ring
    _ ≥ 4 := by norm_num


example {a b : ℕ} (h1 : b = a^2) (h2: a ≥ 2) : b ≥ 4 :=
  calc
    b = a^2 := by rw [h1]
    _ ≥ (2)^2 := by rel [h2]
    _ = 4 := by norm_num
