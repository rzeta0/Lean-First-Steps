-- 21 - Recursion

import Mathlib.Tactic

def f : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 * n + f n

#eval f 2

example {n: ℕ} : f n = n^2 := by
  induction n with
  | zero =>
    calc
      f 0 = 0 := by rw [f]
      _ = 0^2 := by norm_num
  | succ n ih =>
    calc
      f (n + 1) = 1 + 2 * n + f n := by rw [f]
      _ = 1 + 2 * n + n^2 := by rw [ih]
      _ = (n + 1)^2 := by ring
