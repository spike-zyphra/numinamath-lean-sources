import Mathlib

open Real Set
open scoped Real

theorem algebra_277602 :
  sqrt (1 - 2 * sin (20 * π / 180) * cos (20 * π / 180)) /
  (cos (20 * π / 180) - sqrt (1 - (cos (160 * π / 180))^2)) = 1 := by
  have h1 : 1 - 2 * sin (20 * π / 180) * cos (20 * π / 180) = (cos (20 * π / 180) - sin (20 * π / 180)) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (20 * π / 180), sq_nonneg (cos (20 * π / 180) - sin (20 * π / 180)), sq_nonneg (cos (20 * π / 180) + sin (20 * π / 180))]
  have h2 : sqrt (1 - 2 * sin (20 * π / 180) * cos (20 * π / 180)) = cos (20 * π / 180) - sin (20 * π / 180) := by
    rw [h1]
    have h6 : cos (20 * π / 180) > sin (20 * π / 180) := by
      have h7 : sin (20 * π / 180) = cos (70 * π / 180) := by
        have h8 : sin (20 * π / 180) = cos (Real.pi / 2 - (20 * π / 180)) := by
          rw [← cos_pi_div_two_sub]
        have h9 : Real.pi / 2 - (20 * π / 180) = (70 * π / 180) := by
          nlinarith [Real.pi_pos]
        rw [h9] at h8
        linarith
      have h10 : 20 * π / 180 < Real.pi / 2 := by
        linarith [Real.pi_pos]
      have h11 : 70 * π / 180 < Real.pi / 2 := by
        linarith [Real.pi_pos]
      have h12 : cos (20 * π / 180) > cos (70 * π / 180) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
        all_goals
          linarith [Real.pi_pos]
      linarith [h7, h12, Real.sin_sq_add_cos_sq (20 * π / 180)]
    have h5 : cos (20 * π / 180) - sin (20 * π / 180) ≥ 0 := by
      linarith [h6]
    rw [Real.sqrt_sq (by linarith [h6, h5])]
  have h3 : cos (160 * π / 180) = -cos (20 * π / 180) := by
    have h4 : 160 * π / 180 = Real.pi - (20 * π / 180) := by 
      nlinarith [Real.pi_pos]
    rw [h4]
    rw [cos_pi_sub]
  have h4 : 1 - (cos (160 * π / 180))^2 = (sin (20 * π / 180))^2 := by
    rw [h3]
    have h5 : 1 - (-cos (20 * π / 180)) ^ 2 = (sin (20 * π / 180))^2 := by 
      have h6' : sin (20 * π / 180) ^ 2 + cos (20 * π / 180) ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq (20 * π / 180)
      nlinarith
    linarith [h5]
  have h5 : sqrt (1 - (cos (160 * π / 180))^2) = sin (20 * π / 180) := by
    rw [h4]
    have h8 : sin (20 * π / 180) ≥ 0 := by
      apply sin_nonneg_of_nonneg_of_le_pi
      all_goals
        linarith [Real.pi_pos]
    rw [Real.sqrt_sq (by linarith [h8, Real.sin_sq_add_cos_sq (20 * π / 180)])]
  rw [h2, h5]
  have h6' : cos (20 * π / 180) - sin (20 * π / 180) ≠ 0 := by
    have h7 : cos (20 * π / 180) > sin (20 * π / 180) := by
      have h7 : sin (20 * π / 180) = cos (70 * π / 180) := by
        have h8 : sin (20 * π / 180) = cos (Real.pi / 2 - (20 * π / 180)) := by
          rw [← cos_pi_div_two_sub]
        have h9 : Real.pi / 2 - (20 * π / 180) = (70 * π / 180) := by
          nlinarith [Real.pi_pos]
        rw [h9] at h8
        linarith
      have h10 : 20 * π / 180 < Real.pi / 2 := by
        linarith [Real.pi_pos]
      have h11 : 70 * π / 180 < Real.pi / 2 := by
        linarith [Real.pi_pos]
      have h12 : cos (20 * π / 180) > cos (70 * π / 180) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
        all_goals 
          linarith [Real.pi_pos]
      linarith [h7, h12, Real.sin_sq_add_cos_sq (20 * π / 180)]
    intro h
    linarith
  field_simp [h6']
  <;> nlinarith [Real.sin_sq_add_cos_sq (20 * π / 180)]