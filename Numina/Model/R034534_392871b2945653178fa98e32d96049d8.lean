import Mathlib

theorem number_theory_176661 : 
  ∃ n : ℕ, (Nat.digits 10 (n ^ 2)).sum = 100 := by
  by_contra h
  exfalso
  apply h
  use 10111111111 
  native_decide