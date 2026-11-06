import Mathlib

theorem number_theory_161231 {n : ℕ} (hn : n ≠ 0) :
    Nat.totient n = n * ∏ p in n.primeFactors, (1 - 1 / p : ℚ) := by 
  rw [Nat.totient_eq_mul_prod_factors n]
  <;> norm_num
  <;> try native_decide