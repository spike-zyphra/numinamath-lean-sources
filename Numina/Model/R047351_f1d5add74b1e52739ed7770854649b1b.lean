import Mathlib

open Nat Finset

theorem number_theory_608227 (n : ℕ) (hn : n > 0) : n.divisors.sum φ = n := by
  apply Nat.sum_totient