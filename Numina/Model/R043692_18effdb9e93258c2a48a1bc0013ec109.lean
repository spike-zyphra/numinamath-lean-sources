import Mathlib

open Real
open scoped BigOperators

theorem algebra_154642 (A B C : EuclideanSpace ℝ (Fin 3))
  (hA : A = ![1, -2, 3]) (hB : B = ![0, -1, 2]) (hC : C = ![3, -4, 5]) :
  (inner (B - A) (C - A)) / (norm (B - A) * norm (C - A)) = -1 := by 
  rw [hA, hB, hC]
  simp [Fin.sum_univ_three, inner, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  have h1 : sqrt (3 * (12 : ℝ)) = 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> linarith 
  have h2 : sqrt (3 : ℝ) * sqrt (12 : ℝ) = 6 := by
    have h3 : sqrt (3 : ℝ) * sqrt (12 : ℝ) = sqrt (3 * (12 : ℝ)) := by
      rw [← Real.sqrt_mul (by norm_num)]
      all_goals norm_num
    rw [h3]
    rw [show (3 * (12 : ℝ)) = (36 : ℝ) by norm_num]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> linarith 
  field_simp [h2]
  <;> norm_num [h1, h2] 
  <;> linarith 
  all_goals linarith