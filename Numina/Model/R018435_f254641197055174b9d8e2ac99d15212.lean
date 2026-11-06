import Mathlib

theorem number_theory_128673 :
    ∃ n, n ∈ Finset.Icc 1 100000001 ∧ (Nat.fib n) % 10000 = 0 := by 
  use 7500
  constructor 
  · -- Show that 7500 is in the interval [1, 100000001]
    native_decide 
  · -- Show that Nat.fib 7500 % 10000 = 0 
    native_decide