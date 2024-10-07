import Mathlib.Tactic

---

example {n : ℕ} : ∃ k: ℕ, n^2 + n = 2*k := by
  have h : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := Nat.even_or_odd' n
  obtain ⟨m , hm⟩ := h
  obtain ha | hb := hm
  · use 2*m^2 + m
    calc
      n^2 + n = (2*m)^2 + (2*m) := by rw [ha]
      _ = 4*m^2 + 2*m := by ring
      _ = 2*(2*m^2 + m) := by ring
  · use 2*m^2 + 3*m + 1
    calc
      n^2 + n = (2*m + 1)^2 + (2*m + 1) := by rw [hb]
      _ = 4*m^2 + 4*m + 1 + 2*m + 1 := by ring
      _ = 2*(2*m^2 + 3*m + 1) := by ring

--


example {n : ℕ} : n^2 ≠ 2 := by
  -- have h := le_or_succ_le n 1
  have h := le_or_lt n 1
  obtain ha | hb := h
  · apply ne_of_lt
    calc
      n^2 ≤ (1)^2 := by rel [ha]
      _ < 2 := by norm_num
  · apply ne_of_gt
    have h2 := Nat.succ_le_of_lt hb
    calc
      n^2 ≥ (2)^2 := by rel [h2]
      _ > 2 := by norm_num

---
