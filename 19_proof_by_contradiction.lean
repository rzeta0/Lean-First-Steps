-- 19 - Proof by Contradiction

import Mathlib.Tactic

example {a b : ℕ} (h1: a = 5 → b = 6) (h2: b = 7) : ¬ a = 5 := by
  by_contra g
  apply h1 at g
  have h2x : ¬ b = 7 := by linarith
  contradiction
