-- 12 - Definition: Odd Number

import Mathlib.Tactic

example  : Odd 13 := by
  dsimp [Odd]
  use 6
  calc
    13 = 2*6 + 1 := by ring

-- shorter version

example  : Odd 13 := by
  dsimp [Odd]
  use 6
  ring
