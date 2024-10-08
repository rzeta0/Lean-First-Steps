-- 12 - Using Lemmas: Not Equal from Less Than

import Mathlib.Tactic

example {n : ℕ} (h: n < 5): n ≠ 5 := by
  apply ne_of_lt
  exact h


-- longer version with a calc section

example {n : ℕ} (h: n < 5): n ≠ 5 := by
  apply ne_of_lt
  calc
    n < 5 := by rel [h]
