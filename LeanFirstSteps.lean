import Mathlib.Tactic


-- inspired by https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/mathlib.20version.20of.20.60le_or_succ_le.60/near/474138016
lemma le_or_succ_le (a b: ℕ): a ≤ b ∨ b + 1 ≤ a := by
  rw [Nat.succ_le]
  exact le_or_lt a b
