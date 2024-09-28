-- 12 - Using Lemmas: Not Equal from Less Than

import Mathlib.Tactic

example {n : ℕ} (h: n = 1): n ≠ 3 := by
  apply ne_of_lt
  calc
    n = 1 := by rw [h]
    _ < 3 := by norm_num
