import Mathlib

open Polynomial 

theorem algebra_15675 : {n : ℕ| ((X + C (4: ℝ)) * (C 2 * X ^ 2 + C 3 * X + C 9) - C (3 : ℝ) * (X ^ 3 - C 2 * X ^ 2 + C 7 * X) ).coeff n ≠ 0 }.ncard = 3 := by 
  have eq : ((X + C (4: ℝ)) * (C 2 * X ^ 2 + C 3 * X + C 9) - C (3 : ℝ) * (X ^ 3 - C 2 * X ^ 2 + C 7 * X) ) = (-X ^ 3 + 17 * X ^ 2 + 36 : ℝ[X]) := by
    apply Polynomial.funext
    intro x
    simp [pow_succ, pow_zero, mul_add, add_mul, mul_assoc]
    ring
  rw [eq]
  have h3 : {n : ℕ | ((-X ^ 3 + 17 * X ^ 2 + 36 : ℝ[X]) ).coeff n ≠ 0 } = {0, 2, 3} := by
    ext n
    simp [coeff_eq_zero_of_natDegree_lt, natDegree_add_eq_left_of_degree_lt, natDegree_mul, degree_mul, degree_X, degree_C]
    all_goals
      try { 
        cases n with
        | zero =>
          norm_num [coeff_eq_zero_of_natDegree_lt]
        | succ n =>
          cases n with
          | zero =>
            norm_num [coeff_eq_zero_of_natDegree_lt]
          | succ n =>
            cases n with
            | zero =>
              norm_num [coeff_eq_zero_of_natDegree_lt]
            | succ n =>
              simp_all [coeff_eq_zero_of_natDegree_lt]
              all_goals
                try { tauto }
      }
  rw [h3]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> norm_num