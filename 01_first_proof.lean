-- 01 - First Proof

import Mathlib.Tactic

example {a: ℕ} (h1: a = 4) : a > 1 := by linarith
