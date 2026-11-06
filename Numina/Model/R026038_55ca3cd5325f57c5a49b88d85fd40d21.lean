import Mathlib

open Real Set
open scoped Real

theorem algebra_315014 : cot (10 * π / 180) - 4 * cos (10 * π / 180) = sqrt 3 := by
  have h1 : cot (10 * π / 180) = cos (10 * π / 180) / sin (10 * π / 180) := by
    rw [cot_eq_cos_div_sin]
  rw [h1]
  have h2 : sin (10 * π / 180) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals
      nlinarith [Real.pi_pos, Real.pi_gt_three]
  have h2' : sin (10 * π / 180) ≠ 0 := by
    linarith [h2]
  have eq1 : cos (10 * π / 180) - 4 * cos (10 * π / 180) * sin (10 * π / 180) = Real.sqrt 3 * sin (10 * π / 180) := by
    have h3 : sin (20 * π / 180) = 2 * sin (10 * π / 180) * cos (10 * π / 180) := by
      have h4 : 20 * π / 180 = 2 * (10 * π / 180) := by
        ring_nf
      rw [h4]
      rw [sin_two_mul]
      <;> ring_nf
    have h5 : sin (20 * π / 180) = sin (π / 6 - (10 * π / 180)) := by
      ring_nf
    have h6 : sin (π / 6 - (10 * π / 180)) = sin (π / 6) * cos (10 * π / 180) - cos (π / 6) * sin (10 * π / 180) := by
      rw [sin_sub]
    have h7 : sin (π / 6) = 1 / 2 := by
      exact sin_pi_div_six
    have h8 : cos (π / 6) = Real.sqrt 3 / 2 := by
      exact cos_pi_div_six
    rw [h7, h8] at h6
    have h7 : sin (20 * π / 180) = (1 / 2) * cos (10 * π / 180) - (Real.sqrt 3 / 2) * sin (10 * π / 180) := by
      rw [h5, h6]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by nlinarith : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by nlinarith : (3 : ℝ) ≥ 0), Real.sin_sq_add_cos_sq (10 * π / 180), Real.sin_sq_add_cos_sq (20 * π / 180), Real.sin_sq_add_cos_sq (π / 6)]
  have eq4 : cos (10 * π / 180) / sin (10 * π / 180) - 4 * cos (10 * π / 180) = (cos (10 * π / 180) - 4 * cos (10 * π / 180) * sin (10 * π / 180)) / sin (10 * π / 180) := by
    field_simp [h2']
    <;> ring_nf
  rw [eq4]
  rw [eq1]
  field_simp [h2']