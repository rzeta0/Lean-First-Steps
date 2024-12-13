-- 19 - Proof by Contradiction

import Mathlib.Tactic

example {a b : ℕ} (h1: a = 5 → b = 6) (h2: b = 7) : ¬ a = 5 := by
  intro g
  apply h1 at g
  have g1 : b ≠ 7 := by linarith
  rw [ne_eq] at g1
  contradiction
