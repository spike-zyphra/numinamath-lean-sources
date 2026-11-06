import Mathlib

theorem number_theory_304305 : ∃n, Nat.fib n % 1000 = 0 := by 
  use 0 
  simp [Nat.fib_zero]