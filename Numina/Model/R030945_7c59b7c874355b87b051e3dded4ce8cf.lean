import Mathlib

theorem number_theory_226523 (n : ℕ) :
    ∃ k, n ∣ Nat.fib k := by 
  use 0
  simp