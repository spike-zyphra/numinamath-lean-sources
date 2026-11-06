import Mathlib

theorem number_theory_4490 : ¬{x | Nat.Prime x}.Finite := by 
  apply Nat.infinite_setOf_prime