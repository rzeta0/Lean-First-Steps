-- 13 - Lemma: Not Equal from Less Than

import Mathlib.Tactic

example {n : ℕ} (h : n < 5): n ≠ 5 := by
  apply ne_of_lt
  exact h
