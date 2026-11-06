import Mathlib

open BigOperators

theorem number_theory_4861 : ∀ (n : ℕ), ↑(Nat.totient n) =
    ↑n * ∏ p in n.primeFactors, (1 - (p : ℚ)⁻¹) := by 
  intro n 
  rw [Nat.totient_eq_mul_prod_factors]
  all_goals norm_num
  <;> try native_decide