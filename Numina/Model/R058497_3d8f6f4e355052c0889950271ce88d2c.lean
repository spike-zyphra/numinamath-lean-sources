import Mathlib

theorem number_theory_223703 : ∀ n : ℕ, ∃ p > n, p.Prime := by 
  intro n
  apply Nat.exists_infinite_primes