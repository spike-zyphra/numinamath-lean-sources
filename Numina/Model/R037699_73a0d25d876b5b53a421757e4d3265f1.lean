import Mathlib

open Real Set
open scoped Real

theorem algebra_259400 : tan (15 * π / 180) + 1 / tan (15 * π / 180) = 4 := by

  have h1 : tan (15 * π / 180) = sin (15 * π / 180) / cos (15 * π / 180) := by
    rw [tan_eq_sin_div_cos]

  rw [h1]

  have h2 : sin (15 * π / 180) > 0 := by
    have h3 : 0 < (15 * π / 180 : ℝ) := by
      have hpi : 0 < π := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h4 : sin (15 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [Real.pi_gt_three]
    linarith

  have h3 : cos (15 * π / 180) > 0 := by
    have h3 : 0 < (15 * π / 180 : ℝ) := by
      have hpi : 0 < π := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h4 : cos (15 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith [Real.pi_gt_three]
    linarith

  have h4 : sin (15 * π / 180) * cos (15 * π / 180) = 1 / 4 := by
    have h5 : sin (30 * π / 180) = 1 / 2 := by
      have h6 : 30 * π / 180 = π / 6 := by 
        nlinarith [Real.pi_pos]
      rw [h6]
      have h7 : sin (π / 6) = 1 / 2 := by 
        exact sin_pi_div_six
      linarith [h7]

    have h8 : sin (30 * π / 180) = 2 * sin (15 * π / 180) * cos (15 * π / 180) := by
      have h9 : 30 * π / 180 = 2 * (15 * π / 180) := by 
        nlinarith [Real.pi_pos]
      rw [h9]
      rw [sin_two_mul]

    nlinarith [h5, h8]

  have h5 : sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 = 1 := by
    have h6 : sin (15 * π / 180) ^ 2 + cos (15 * π / 180) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (15 * π / 180)
    linarith

  field_simp [show sin (15 * π / 180) ≠ 0 by linarith, show cos (15 * π / 180) ≠ 0 by linarith]
  <;> nlinarith [h4, h5]