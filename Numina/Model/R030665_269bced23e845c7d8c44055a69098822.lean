import Mathlib

theorem number_theory_6920 : Set.Infinite { p : ℕ | p.Prime } := by
  apply Nat.infinite_setOf_prime