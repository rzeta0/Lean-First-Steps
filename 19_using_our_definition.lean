-- 19 - Using Our Definition

import Mathlib.Tactic

---

def Triangle (a : ℕ) : Prop := ∃ n, 2 * a = n * (n + 1)

---

example {t : ℕ} (h1: Triangle t) : Triangle (9*t + 1) := by
  dsimp [Triangle] at *
  obtain ⟨s, hs⟩ := h1
  use 3*s + 1
  calc
    2 * (9 * t + 1) = 9 * (2 * t) + 2 := by ring
    _ = 9 * (s * (s + 1)) + 2 := by rw [hs]
    _ = 9*s^2 + 9*s + 2 := by ring
    _ = ((3*s + 1)) * ((3*s + 1) + 1) := by ring
