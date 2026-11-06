import Mathlib

theorem number_theory_6392 : Set.Infinite {p : ℕ | p.Prime ∧ p ≡ 1 [MOD 4]} := by
  apply Nat.infinite_setOf_prime_modEq_one
  all_goals norm_num