import Mathlib

theorem algebra_167289 (f : ℝ → ℝ) (hf2 : f 2 = 1) (hf4 : f 4 = 15) (hf5 : f 5 = 28) :
    ∃ P : Polynomial ℝ, P.degree = 2 ∧ P.coeff 2 = 2 ∧ P.coeff 1 = -5 ∧ P.coeff 0 = 3 := by
  use Polynomial.C (3 : ℝ) + Polynomial.C (-5 : ℝ) * Polynomial.X + Polynomial.C (2 : ℝ) * Polynomial.X ^ 2
  constructor
  · -- Show that the degree is 2
    compute_degree!
    all_goals norm_num
  constructor
  · -- Show that the coefficient of 2 is 2
    norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt]
    all_goals norm_num
  constructor
  · -- Show that the coefficient of 1 is -5
    norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt]
    all_goals norm_num
  · -- Show that the coefficient of 0 is 3
    norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt]
    all_goals norm_num