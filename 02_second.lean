-- 02 - Symbols, No Numbers

import Mathlib.Tactic

example {x y z c: ℝ} (h1 : z = y^2) (h2: y = x + c) : z = (x + c)^2 :=
  calc
    z = y^2 := by rw [h1]
    _ = (x+c)^2 := by rw [h2]
