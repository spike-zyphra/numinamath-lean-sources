import Mathlib

open Real Set
open scoped Real

theorem algebra_188151 : (tan (20 * π / 180) ^ 2 - sin (20 * π / 180) ^ 2) / (tan (20 * π / 180) ^ 2 * sin (20 * π / 180) ^ 2) = 1 := by

  have htan : tan (20 * π / 180) = sin (20 * π / 180) / cos (20 * π / 180) := by
    rw [tan_eq_sin_div_cos]

  rw [htan]

  have h1 : sin (20 * π / 180) ≠ 0 := by
    have h2 : 0 < (20 * π / 180 : ℝ) := by 
      have h3 : π > 0 := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h3 : sin (20 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith
      have h4 : 0 < π := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    linarith

  have h2 : cos (20 * π / 180) ≠ 0 := by 
    have h5 : 0 < (20 * π / 180 : ℝ) := by 
      have h3 : π > 0 := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h6 : cos (20 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_gt_three, Real.pi_pos]
    linarith

  have eq3 : ( (sin (20 * π / 180) / cos (20 * π / 180) ) ^ 2 - sin (20 * π / 180) ^ 2 ) =
      (sin (20 * π / 180) ^ 4) / (cos (20 * π / 180) ^ 2) := by
    field_simp [h2, h1]
    <;> nlinarith [Real.sin_sq_add_cos_sq (20 * π / 180), sq_nonneg (sin (20 * π / 180) ^ 2), sq_nonneg (cos (20 * π / 180) ^ 2), sq_pos_of_ne_zero (show sin (20 * π / 180) ≠ 0 by exact h1), sq_pos_of_ne_zero (show cos (20 * π / 180) ≠ 0 by exact h2) ]

  have eq4 : ( (sin (20 * π / 180) / cos (20 * π / 180) ) ^ 2 * sin (20 * π / 180) ^ 2 ) = (sin (20 * π / 180) ^ 4) / (cos (20 * π / 180) ^ 2) := by
    field_simp [h2, h1]
    <;> nlinarith [Real.sin_sq_add_cos_sq (20 * π / 180), sq_nonneg (sin (20 * π / 180) ^ 2), sq_nonneg (cos (20 * π / 180) ^ 2), sq_pos_of_ne_zero (show sin (20 * π / 180) ≠ 0 by exact h1), sq_pos_of_ne_zero (show cos (20 * π / 180) ≠ 0 by exact h2) ]

  rw [eq3, eq4]

  have eq5 : ( (sin (20 * π / 180) ^ 4) / (cos (20 * π / 180) ^ 2) ) / ( (sin (20 * π / 180) ^ 4) / (cos (20 * π / 180) ^ 2) ) = 1 := by
    have h3 : (sin (20 * π / 180) ^ 4) / (cos (20 * π / 180) ^ 2) ≠ 0 := by
      have h4 : sin (20 * π / 180) ^ 4 > 0 := by
        have h51 : sin (20 * π / 180) > 0 := by
          apply sin_pos_of_pos_of_lt_pi
          linarith [Real.pi_pos, Real.pi_gt_three]
          nlinarith [Real.pi_pos, Real.pi_gt_three]
        positivity
      have h5 : cos (20 * π / 180) ^ 2 > 0 := by 
        have h61 : cos (20 * π / 180) > 0 := by
          apply cos_pos_of_mem_Ioo
          constructor <;> nlinarith [Real.pi_gt_three, Real.pi_pos]
        positivity
      have hne : sin (20 * π / 180) ^ 4 / cos (20 * π / 180) ^ 2 ≠ 0 := by
        apply div_ne_zero
        linarith
        linarith
      exact hne

    field_simp [h3]

  exact eq5