import Mathlib

theorem number_theory_7920 (n : ℕ) : ∃ p > n, p.Prime := by
  apply Nat.exists_infinite_primes