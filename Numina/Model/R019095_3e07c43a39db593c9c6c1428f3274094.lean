import Mathlib

open Real Set
open scoped Real

theorem algebra_100658 : 3 / sin (π / 9)^2 - 1 / cos (π / 9)^2 + 64 * sin (π / 9)^2 = 32 := by 
  have h1 : sin (π / 9) > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h2 : cos (π / 9) > 0 := by 
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h3 : sin (3 * (π / 9)) = 3 * sin (π / 9) - 4 * sin (π / 9) ^ 3 := by 
    rw [sin_three_mul]
  have h4 : cos (3 * (π / 9)) = 4 * cos (π / 9) ^ 3 - 3 * cos (π / 9) := by 
    rw [cos_three_mul]
  have h5 : sin (3 * (π / 9)) = Real.sqrt 3 / 2 := by
    have h6 : 3 * (π / 9) = Real.pi / 3 := by 
      ring
    rw [h6]
    exact sin_pi_div_three
  have h7 : cos (3 * (π / 9)) = 1 / 2 := by
    have h8 : 3 * (π / 9) = Real.pi / 3 := by 
      ring
    rw [h8]
    exact cos_pi_div_three
  -- Check sin and cos with square.
  have h8 : sin (π / 9) ^ 2 + cos (π / 9) ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq (π / 9)
  -- Next step with field_simp
  field_simp [show sin (π / 9) ≠ 0 by linarith, show cos (π / 9) ≠ 0 by linarith]
  -- Final step with ring_nf and norm_num
  nlinarith [Real.sin_sq_add_cos_sq (π / 9), sq_nonneg (sin (π / 9) ^ 2 - 1 / 4), sq_nonneg (cos (π / 9) ^ 2 - 3 / 4), sq_nonneg (sin (π / 9) - Real.sqrt (1 / 4)), sq_nonneg (cos (π / 9) ^ 2 - 3 / 4), Real.sqrt_pos.mpr (show (0: ℝ) < 3 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ 3 by norm_num)]