import Mathlib

open Real

theorem algebra_303774 : sin (7.5 * π / 180) + cos (7.5 * π / 180) = (Real.sqrt (4 + Real.sqrt 6 - Real.sqrt 2)) / 2 := by

  have h1 : sin (7.5 * π / 180) + cos (7.5 * π / 180) = Real.sqrt ((sin (7.5 * π / 180) + cos (7.5 * π / 180)) ^ 2) := by
    have h2 : sin (7.5 * π / 180) > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    have h3 : cos (7.5 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_pos]
    have h4 : (sin (7.5 * π / 180) + cos (7.5 * π / 180)) > 0 := by linarith
    rw [Real.sqrt_sq (by linarith)]

  have h2 : (sin (7.5 * π / 180) + cos (7.5 * π / 180)) ^ 2 = (4 + Real.sqrt 6 - Real.sqrt 2) / 4 := by
    have h3 : sin (7.5 * π / 180) ^ 2 + cos (7.5 * π / 180) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (7.5 * π / 180)
    have h5_5 : 2 * (sin (7.5 * π / 180) * cos (7.5 * π / 180)) = sin (2 * (7.5 * π / 180)) := by
      calc
        2 * (sin (7.5 * π / 180) * cos (7.5 * π / 180)) 
            = 2 * sin (7.5 * π / 180) * cos (7.5 * π / 180) := by ring
        _ = sin (2 * (7.5 * π / 180)) := by 
          rw [show 2 * (7.5 * π / 180) = 2 * (7.5 * π / 180) by rfl]
          have h7 : sin (2 * (7.5 * π / 180)) = 2 * sin (7.5 * π / 180) * cos (7.5 * π / 180) := by
            rw [sin_two_mul]
          linarith [h7]
    have h5 : sin (2 * (7.5 * π / 180)) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
      have h51 : 2 * (7.5 * π / 180) = (Real.pi / 12) := by
        ring_nf
      rw [h51]
      have h2 : sin (Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
        have h1 : sin (Real.pi / 12) = sin (Real.pi / 4 - Real.pi / 6) := by
          ring_nf
        rw [h1]
        rw [sin_sub]
        have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
          rw [sin_pi_div_four]
        have h4 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
          rw [cos_pi_div_four]
        have h5 : sin (Real.pi / 6) = 1 / 2 := by
          rw [sin_pi_div_six]
        have h6 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := by
          rw [cos_pi_div_six]
        rw [h3, h4, h5, h6]
        have h10 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
          calc
            Real.sqrt 2 * Real.sqrt 3 = Real.sqrt (2 * 3 : ℝ) := by 
              rw [Real.sqrt_mul (by norm_num)]
            _ = Real.sqrt (6 : ℝ) := by norm_num
        nlinarith [h10, Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith
    have h6 : (sin (7.5 * π / 180) + cos (7.5 * π / 180)) ^ 2 = sin (7.5 * π / 180) ^ 2 + cos (7.5 * π / 180) ^ 2 + 2 * (sin (7.5 * π / 180) * cos (7.5 * π / 180)) := by
      ring
    rw [h6, h3]
    have h7 : 2 * (sin (7.5 * π / 180) * cos (7.5 * π / 180)) = sin (2 * (7.5 * π / 180)) := h5_5
    have h8 : sin (2 * (7.5 * π / 180)) = (Real.sqrt 6 - Real.sqrt 2) / 4 := h5
    linarith [h7, h8]
  have h3 : Real.sqrt (( (4 + Real.sqrt 6 - Real.sqrt 2) / 4 )) = (Real.sqrt (4 + Real.sqrt 6 - Real.sqrt 2)) / 2 := by
    have h4 : Real.sqrt (( (4 + Real.sqrt 6 - Real.sqrt 2) / 4 )) = Real.sqrt (4 + Real.sqrt 6 - Real.sqrt 2) / Real.sqrt 4 := by
      field_simp [Real.sqrt_div]
    have h5 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h4, h5]
  rw [h1, h2, h3]
  all_goals nlinarith [Real.sqrt_nonneg (4 + Real.sqrt 6 - Real.sqrt 2), 
        Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (4 + Real.sqrt 6 - Real.sqrt 2 : ℝ) by nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, sq_nonneg (Real.sqrt 6 - Real.sqrt 2), sq_nonneg (Real.sqrt 6 + Real.sqrt 2)]), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]