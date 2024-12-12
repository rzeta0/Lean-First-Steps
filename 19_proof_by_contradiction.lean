-- 19 - Proof by Contradiction

import Mathlib.Tactic

example {a b : ℕ} (h1: a = 5 → b = 6) (h2: b = 7) : ¬ a = 5 := by
  intro g
  apply h1 at g
  have g1 : b ≠ 7 := by linarith
  rw [ne_eq] at g1
  contradiction


--

example {x : ℝ} (h1 : (x + 3) * (x - 3) = 0) (h2 : ¬ x = 3) : x = - 3 := by
  rw [mul_eq_zero] at h1
  obtain ga | gb := h1
  · linarith
  · have gc: x = 3 := by linarith
    contradiction

--

example {a : ℕ} (h: ¬ a = 5) : ¬ a = 5 := by
  intro g
  contradiction
