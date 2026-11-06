import Mathlib

open Finset

theorem number_theory_5401 {N : ℕ} (hN : N ≠ 0) :
    N.totient = N * ∏ p ∈ N.primeFactors, (1 - 1 / p : ℚ) := by
  rw [Nat.totient_eq_mul_prod_factors]
  all_goals norm_num