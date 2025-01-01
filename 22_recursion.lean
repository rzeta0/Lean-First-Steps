-- 21 - Recursion

import Mathlib.Tactic

def fₙ : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 * n + fₙ n

#eval fₙ 2

example {n: ℕ} : fₙ n = n^2 := by
  induction n with
  | zero =>
    calc
      fₙ 0 = 0 := by rw [fₙ]
      _ = 0^2 := by norm_num
  | succ n ih =>
    calc
      fₙ (n + 1) = 1 + 2 * n + fₙ n := by rw [fₙ]
      _ = 1 + 2 * n + n^2 := by rw [ih]
      _ = (n + 1)^2 := by ring
