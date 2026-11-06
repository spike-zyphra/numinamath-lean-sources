import Mathlib

theorem algebra_100222 {u : ℕ → ℝ} (hu1 : u 1 = 5)
    (hun : ∀ n ≥ 1, u (n + 1) - u n = 3 + 4 * (n - 1)) :
    ∃ p : Polynomial ℝ, p.eval 1 = u 1 ∧ p.eval 2 = u 2 ∧ p.eval 3 = u 3 ∧
    p.coeff 0 + p.coeff 1 + p.coeff 2 = 5 := by

  have u1 : u 1 = 5 := hu1
  have u2 : u 2 = 8 := by 
    have eq1 := hun 1 (by norm_num)
    norm_num at eq1
    linarith [eq1, u1]

  have u3 : u 3 = 15 := by 
    have eq2 := hun 2 (by norm_num)
    norm_num at eq2
    linarith [eq2, u2]

  use (Polynomial.C (6 : ℝ) + Polynomial.C (-3) * Polynomial.X + Polynomial.C (2) * Polynomial.X ^ 2)
  constructor
  · -- Verify that p.eval 1 = u1
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num [u1]
  constructor
  · -- Verify that p.eval 2 = u2
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num [u2]
  constructor
  · -- Verify that p.eval 3 = u3
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    norm_num [u3]
  · -- Verify that the sum of the coefficients is 5
    simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.natDegree]
    <;> norm_num
    <;> ring_nf
    <;> norm_num