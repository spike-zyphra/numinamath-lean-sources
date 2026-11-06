import Mathlib

theorem number_theory_131007 : ∀ n : ℕ, ∃ p > n, p.Prime := by 
  intro n 
  apply Nat.exists_infinite_primes