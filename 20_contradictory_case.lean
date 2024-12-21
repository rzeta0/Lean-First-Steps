-- 20 - Contradictory Cases

import Mathlib.Tactic

example (P : Prop) : ¬ (¬ P) → P := by
  intro g
  by_cases h1 : P
  · exact h1
  · contradiction
