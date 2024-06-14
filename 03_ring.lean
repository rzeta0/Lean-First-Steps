-- 03 - Algebra with ring

import Mathlib.Tactic


example {x y z c: ℝ} (h1 : z = y^2) (h2: y = x + c) : z = x^2 + c^2 + 2*x*c :=
  calc
    z = y^2 := by rw [h1]
    _ = (x+c)^2 := by rw [h2]
    _ = x^2 + c^2 + 2*x*c := by ring


example {y a b : ℝ} (h1 : y = (a - b) * (a + b)) : y = a^2 - b^2 :=
  calc
    y = (a - b) * (a + b) := by rw [h1]
    _ = a^2 - a*b + a*b - b^2 := by ring
    _ = a^2 - b^2 := by ring
