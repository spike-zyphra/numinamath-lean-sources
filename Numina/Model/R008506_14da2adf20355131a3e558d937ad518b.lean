import Mathlib

open Nat

theorem number_theory_4480 (n : ℕ) : ∃ p > n, p.Prime := by
  apply Nat.exists_infinite_primes