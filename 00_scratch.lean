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
