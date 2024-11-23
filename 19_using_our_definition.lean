-- 19 - Using Our Definition

import Mathlib.Tactic

---

def Triangle (a : ℕ) : Prop := ∃ n, 2 * a = n * (n + 1)

---

example {t : ℕ} (h1: Triangle t) : Triangle (9*t + 1) := by
  dsimp [Triangle] at *
  obtain ⟨m, hm⟩ := h1
  use 3*m + 1
  calc
    2 * (9 * t + 1) = 9 * (2 * t) + 2 := by ring
    _ = 9 * (m * (m + 1)) + 2 := by rw [hm]
    _ = 9*m^2 + 9*m + 2 := by ring
    _ = ((3*m + 1)) * ((3*m + 1) + 1) := by ring
