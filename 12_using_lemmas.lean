-- 12 - Using Lemmas: Not Equal from Less Than

import Mathlib.Tactic

example {n : ℕ} (h: n = 1): n ≠ 5 := by
  apply ne_of_lt
  calc
    n = 1 := by rw [h]
    _ < 5 := by norm_num

---

example {n : ℕ} (h: n = 1): n ≠ 5 := by
  calc
    n = 1 := by rw [h]
    _ ≠ 5 := by norm_num

---

example {n : ℕ} (h: n < 5): n ≠ 5 := by
  apply ne_of_lt
  apply h

--
