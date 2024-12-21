import Mathlib.Tactic

--import LeanFirstSteps

---

lemma Nat.le_or_succ_le' (a b: ℕ): a ≤ b ∨ b + 1 ≤ a := by
  have h : a ≤ b ∨ b < a := le_or_lt a b
  rw [← Nat.succ_le] at h
  exact h

---

lemma Nat.le_or_succ_le (a b: ℕ): a ≤ b ∨ b + 1 ≤ a := by
  rw [Nat.succ_le]
  exact le_or_lt a b

--


---
-- note the 2*a to avoid division by 2 with naturals
def Triangle (a : ℕ) : Prop := ∃ n, 2 * a = n * (n + 1)

example : Triangle 10 := by
  dsimp [Triangle]
  use 4

---

-- src https://www.shyamsundergupta.com/triangle.htm
example {t : ℕ} (h1: Triangle t) : Triangle (9*t + 1) := by
  dsimp [Triangle] at *
  obtain ⟨s, hs⟩ := h1
  use 3*s + 1
  calc
    2 * (9 * t + 1) = 9 * (2 * t) + 2 := by ring
    _ = 9 * (s * (s + 1)) + 2 := by rw [hs]
    _ = 9*s^2 + 9*s + 2 := by ring
    _ = ((3*s + 1)) * ((3*s + 1) + 1) := by ring

---

example {t: ℕ} (h1: Triangle t) : ∃ n, 8 * t + 1 = n^2 := by
  dsimp [Triangle] at *
  obtain ⟨s, hs⟩ := h1
  use 2*s + 1
  calc
    8*t + 1 = 4 * (2 * t) + 1 := by ring
    _ = 4 * (s*(s + 1)) + 1 := by rw [hs]
    _ = 4*s^2 +4*s + 1 := by ring
    _ = (2*s + 1)^2 := by ring

---

-- reductio ad absurdum

example {n : ℕ} (h: n = 5) : ¬ n = 1 := by
  intro hn
  have g :=
    calc
      5 = n := by rw [h]
      _ = 1 := by rw [hn]
  contradiction
  --linarith


----

example {x : ℝ} (h1: x > 0) (h2: x^2 = 3^2): x = 3 := by
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h2
  obtain ha | hb := h2
  · -- x = 3
    exact ha
  · -- x = -3
    have g3:=
      calc
        x = -3 := by rw [hb]
        _ ≤ 0 := by norm_num
    apply not_lt_of_ge at g3
    contradiction


-- shorter version

example {x : ℝ} (h1: x > 0) (h2: x^2 = 3^2): x = 3 := by
  rw [sq_eq_sq_iff_eq_or_eq_neg] at h2
  obtain ha | hb := h2
  · -- x = 3
    exact ha
  · -- x = -3
    linarith

---

-- book example
example (P : Prop) : ¬ (¬ P) ↔ P := by
  by_cases h: P
  · constructor
    · intro g1
      exact h
    · intro g2
      intro f
      contradiction
  · constructor
    · intro g3
      contradiction
    · intro g4
      contradiction


----

example (P : Prop) : P → ¬ (¬ P) := by
  intro g
  by_cases h1 : P
  · by_contra f
    contradiction
  · contradiction

----
