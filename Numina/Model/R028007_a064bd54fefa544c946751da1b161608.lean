import Mathlib

theorem algebra_10582 {f g : Polynomial ℝ} 
  (hf : f = Polynomial.X ^ 4 - 3 * Polynomial.X ^ 3 + 5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 1)
  (hg : g = 2 * Polynomial.X ^ 3 - 3 * Polynomial.X ^ 2 + 4 *Polynomial.X + 7)
  :(f * g).coeff 3 = 19 := by
  rw [hf, hg]
  ring_nf
  <;> simp [Polynomial.coeff_eq_zero_of_natDegree_lt, add_mul, mul_add, mul_assoc]
  <;> norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt, add_mul, mul_add, mul_assoc]
  <;> native_decide