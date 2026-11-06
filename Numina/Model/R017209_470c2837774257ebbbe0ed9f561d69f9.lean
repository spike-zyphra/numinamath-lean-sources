import Mathlib

open Real Set

theorem algebra_313931 : cot (10 * π / 180) - 4 * cos (10 * π / 180) = sqrt 3 := by
  have h1 : sin (10 * π / 180) ≠ 0 := by
    have h1 : sin (10 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · -- Show 0 < 10°
        ring_nf
        linarith [Real.pi_pos]
      · -- Show 10° < π
        ring_nf
        linarith [Real.pi_pos]
    linarith
  have h2 : cos (10 * π / 180) ^ 2 + sin (10 * π / 180) ^ 2 = 1 := Real.cos_sq_add_sin_sq (10 * π / 180)
  have h3 : cot (10 * π / 180) = cos (10 * π / 180) / sin (10 * π / 180) := by
    rw [cot_eq_cos_div_sin]
  rw [h3]
  have eq1 : cos (10 * π / 180) / sin (10 * π / 180) - 4 * cos (10 * π / 180) = (cos (10 * π / 180) - 4 * cos (10 * π / 180) * sin (10 * π / 180)) / sin (10 * π / 180) := by
    field_simp [h1]
    all_goals ring
  rw [eq1]
  have eq2 : cos (10 * π / 180) - 4 * cos (10 * π / 180) * sin (10 * π / 180) = Real.sqrt 3 * sin (10 * π / 180) := by
    have h20 : sin (20 * π / 180) = 2 * sin (10 * π / 180) * cos (10 * π / 180) := by
      have h : sin (2 * (10 * π / 180)) = 2 * sin (10 * π / 180) * cos (10 * π / 180) := by
        rw [sin_two_mul]
      ring_nf at h ⊢
      linarith
    have h30 : sin (20 * π / 180) = sin (π / 6 - (10 * π / 180)) := by
      ring_nf
    have h40 : sin (π / 6 - (10 * π / 180)) = sin (π / 6) * cos (10 * π / 180) - cos (π / 6) * sin (10 * π / 180) := by
      rw [sin_sub]
    have h21 : sin (π / 6) = 1 / 2 := by
      rw [sin_pi_div_six]
    have h22 : cos (π / 6) = Real.sqrt 3 / 2 := by
      rw [cos_pi_div_six]
    rw [h30, h40, h21, h22] at h20
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), Real.sin_sq_le_one (10 * π / 180), Real.cos_sq_le_one (10 * π / 180)]
  have eq3 : (cos (10 * π / 180) - 4 * cos (10 * π / 180) * sin (10 * π / 180)) / sin (10 * π / 180) = Real.sqrt 3 := by
    have eq4 : cos (10 * π / 180) - 4 * cos (10 * π / 180) * sin (10 * π / 180) = Real.sqrt 3 * sin (10 * π / 180) := eq2
    have h12 : sin (10 * π / 180) ≠ 0 := h1
    rw [eq4]
    field_simp [h12]
    all_goals nlinarith
  exact eq3