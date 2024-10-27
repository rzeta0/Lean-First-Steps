-- 12 - Definition: Odd Number

import Mathlib.Tactic

example : Odd (13 : ℤ) := by
  dsimp [Odd]
  use 6
  norm_num
