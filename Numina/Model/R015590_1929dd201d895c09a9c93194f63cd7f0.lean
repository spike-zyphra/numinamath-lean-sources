import Mathlib

open Real Set
open scoped Real

theorem algebra_162181 : (sqrt 3 - 4 * sin (20 * π / 180) + 8 * (sin (20 * π / 180))^3) /
    (2 * sin (20 * π / 180) * sin (480 * π / 180)) = 2 * sqrt 3 / 3 := by
  have h1 : sin (480 * π / 180) = Real.sqrt 3 / 2 := by
    have h2 : 480 * π / 180 = 2 * π + 2 * π / 3 := by 
      linarith [Real.pi_pos]
    rw [h2]
    have h3 : sin (2 * π + 2 * π / 3) = sin (2 * π / 3) := by 
      rw [sin_add, sin_two_pi, cos_two_pi]
      norm_num
    rw [h3]
    have h4 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by 
      have h5 : 2 * π / 3 = π - π / 3 := by 
        ring_nf
      rw [h5]
      rw [sin_pi_sub]
      have h6 : sin (π / 3) = Real.sqrt 3 / 2 := by 
        exact sin_pi_div_three
      rw [h6]
    exact h4
  have h4 : sqrt 3 - 4 * sin (20 * π / 180) + 8 * (sin (20 * π / 180))^3 = 2 * sin (20 * π / 180) := by
    have h60 : sin (60 * π / 180) = Real.sqrt 3 / 2 := by 
      have h12 : 60 * π / 180 = π / 3 := by 
        ring_nf
      rw [h12]
      have h13 : sin (π / 3) = Real.sqrt 3 / 2 := by
        exact sin_pi_div_three
      rw [h13]
    have h61 : 60 * π / 180 = 3 * (20 * π / 180) := by 
      ring_nf
    have h62 : sin (60 * π / 180) = 3 * sin (20 * π / 180) - 4 * (sin (20 * π / 180)) ^ 3 := by 
      rw [h61]
      rw [sin_three_mul]
    rw [h60] at h62
    nlinarith
  have h5 : 2 * sin (20 * π / 180) * sin (480 * π / 180) = Real.sqrt 3 * sin (20 * π / 180) := by 
    rw [h1]
    all_goals ring_nf
  have h7 : sin (20 * π / 180) ≠ 0 := by 
    have h1 : 0 < 20 * π / 180 := by 
      nlinarith [Real.pi_pos]
    have h2 : 20 * π / 180 < Real.pi := by 
      nlinarith [Real.pi_pos]
    have h3 : sin (20 * π / 180) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith
    have h7 : sin (20 * π / 180) ≠ 0 := by 
      linarith
    exact h7
  have eq1 : (sqrt 3 - 4 * sin (20 * π / 180) + 8 * (sin (20 * π / 180))^3) / (2 * sin (20 * π / 180) * sin (480 * π / 180)) = 2 / sqrt 3 := by 
    rw [show sqrt 3 - 4 * sin (20 * π / 180) + 8 * (sin (20 * π / 180))^3 = 2 * sin (20 * π / 180) by linarith [h4], 
        show 2 * sin (20 * π / 180) * sin (480 * π / 180) = Real.sqrt 3 * sin (20 * π / 180) by linarith [h5]]
    have h8 : sin (20 * π / 180) ≠ 0 := h7
    field_simp [h8, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
    <;> ring_nf <;> norm_num [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ))]
  rw [eq1]
  have h8 : (2 : ℝ) / sqrt 3 = 2 * sqrt 3 / 3 := by 
    field_simp [Real.sqrt_pos.2 (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
    <;> nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (3 : ℝ) by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
  rw [h8]