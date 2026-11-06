import Mathlib

theorem algebra_241499 (n : ℤ) (h : n = 30275) :
    ∃ p : Polynomial ℤ, p.degree = 4 ∧ n = p.eval 10 := by 
  rw [h]
  use (Polynomial.C 3 * Polynomial.X^4 + Polynomial.C 0 * Polynomial.X^3 + Polynomial.C 2 * Polynomial.X^2 + Polynomial.C 7 * Polynomial.X + Polynomial.C 5)
  constructor
  · -- Show that the degree is 4
    compute_degree!
  · -- Show that evaluating the polynomial at 10 gives 30275
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]