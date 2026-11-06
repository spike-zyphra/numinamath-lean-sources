import Mathlib

theorem number_theory_226323 {n : ℕ} (hn : n ≠ 0) :
    n.totient = n * ∏ p ∈ n.primeFactors, (1 - 1 / p : ℚ) := by
  rw [Nat.totient_eq_mul_prod_factors]
  all_goals norm_num
  <;> ring