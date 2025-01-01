-- 21 - Recursion

import Mathlib.Tactic

def Fₙ : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 * n + Fₙ n

#eval Fₙ 2

example {n: ℕ} : Fₙ n = n^2 := by
  induction n with
  | zero =>
    calc
      Fₙ 0 = 0 := by rw [Fₙ]
      _ = 0^2 := by norm_num
  | succ n ih =>
    calc
      Fₙ (n + 1) = 1 + 2 * n + Fₙ n := by rw [Fₙ]
      _ = 1 + 2 * n + n^2 := by rw [ih]
      _ = (n + 1)^2 := by ring
