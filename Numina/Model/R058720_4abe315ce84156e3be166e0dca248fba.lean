import Mathlib

theorem algebra_197547 :
    ∃ P : Polynomial ℝ, P.degree = 3 ∧ P.eval 0 = 74 ∧ P.eval 1 = 19 ∧ P.eval 2 = 65 ∧ P.eval 3 = 92 ∧
    P.eval 4 = -20 ∧ P.eval 5 = -391 := by 
  use Polynomial.C (-20 : ℝ) * Polynomial.X ^ 3 + Polynomial.C (110.5 : ℝ) * Polynomial.X ^ 2 + 
    Polynomial.C (-145.5 : ℝ) * Polynomial.X + Polynomial.C (74 : ℝ)
  constructor 
  · -- Show that the degree is 3
    compute_degree!
  constructor
  · -- Show that P(0) = 74
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  constructor
  · -- Show that P(1) = 19
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  constructor
  · -- Show that P(2) = 65
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  constructor
  · -- Show that P(3) = 92
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  constructor
  · -- Show that P(4) = -20
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  · -- Show that P(5) = -391
    norm_num [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]