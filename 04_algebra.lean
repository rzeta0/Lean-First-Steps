-- 04 - Simple Algebra

import Mathlib.Tactic

example {a b : ℤ} : (a - b) * (a + b) = a^2 - b^2 :=
  calc
    (a - b) * (a + b) = a^2 - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring
