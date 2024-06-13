-- 02 - Functions Without Numbers

import Mathlib.Tactic

example {x y z : ℝ} (h1 : z = y^2) (h2: y = x + 2) : z = (x + 2)^2 :=
  calc
    z = y^2 := by rw [h1]
    _ = (x+2)^2 := by rw [h2]
