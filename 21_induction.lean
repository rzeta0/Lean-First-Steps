-- 21 - Simple Induction

import Mathlib.Tactic

example {n : ℕ} : 2^n ≥ n + 1 := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    calc
      2^(n + 1) = 2 * 2^n := by ring
      _ ≥ 2 * (n + 1) := by rel [ih]
      _ = (n + 1) + 1 + n := by ring
      _ ≥ (n + 1) + 1 := by norm_num
