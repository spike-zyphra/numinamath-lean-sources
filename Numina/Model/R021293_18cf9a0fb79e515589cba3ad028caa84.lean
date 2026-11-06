import Mathlib

theorem algebra_21223 (A B C : EuclideanSpace ℝ (Fin 2))
    (hA : A = ![1, 2]) (hB : B = ![7, 10]) (hC : C = ![1, 12]) :
    min (min (dist A B) (dist B C)) (dist A C) = 2 * Real.sqrt 10 := by
  rw [hA, hB, hC]
  simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring_nf
  have h1 : Real.sqrt 100 = 10 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  -- Show sqrt(40) = 2*sqrt(10)
  have h2 : Real.sqrt 40 = 2 * Real.sqrt 10 := by
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : 2 * Real.sqrt 10 ≤ (10 : ℝ) := by
    have h4 : Real.sqrt 10 > 0 := by
      positivity
    nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
  all_goals norm_num [h1, h2, h3]
  <;> ring_nf <;> norm_num <;> ring_nf
  all_goals try { nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)] }