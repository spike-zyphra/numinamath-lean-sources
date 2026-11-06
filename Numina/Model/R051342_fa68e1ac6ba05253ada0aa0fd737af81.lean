import Mathlib

theorem number_theory_7999 (n : ℕ) (hn : n > 0) :
    ∑ d in n.divisors, (Nat.totient d) = n := by 
  apply Nat.sum_totient