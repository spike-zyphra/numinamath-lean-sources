import Mathlib

open Polynomial

theorem algebra_5447 {F : ℝ[X]} (hF : F.degree = 2)
    (hF1 : F.eval 1 = 1^3) (hF2 : F.eval 2 = 2^3) (hF3 : F.eval 3 = 3^3) :
    F.eval 4 = 58 := by

  have h1 : F.natDegree = 2 := by
    rw [natDegree_eq_of_degree_eq_some]
    rw [hF]
    all_goals norm_num

  have hF_eq : ∀ (x : ℝ), F.eval x = F.coeff 2 * x^2 + F.coeff 1 * x + F.coeff 0 := by
    intro x 
    simp [Polynomial.eval_eq_sum_range' (show F.natDegree < (3 : ℕ) by
      rw [h1]
      all_goals
      norm_num
    ), h1, Finset.sum_range_succ, mul_add, add_mul, mul_assoc]
    <;> ring
  
  have eq1 := hF_eq 1
  rw [hF1] at eq1
  
  have eq2 := hF_eq 2
  rw [hF2] at eq2
  
  have eq3 := hF_eq 3
  rw [hF3] at eq3
  
  have eq4 := hF_eq 4
  norm_num at eq1 eq2 eq3 eq4
  
  linarith