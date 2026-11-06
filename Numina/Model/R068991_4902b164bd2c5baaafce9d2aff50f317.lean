import Mathlib

open Real

theorem calculus_11969 : tan (π / 9) + 4 * sin (π / 9) = sqrt 3 := by 
  have htan : tan (π / 9) = sin (π / 9) / cos (π / 9) := by 
    rw [tan_eq_sin_div_cos]
  rw [htan]

  have h1 : 0 < π / 9 := by 
    linarith [Real.pi_pos]

  have h2 : 0 < cos (π / 9) := by 
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]

  have h3 : 0 < sin (π / 9) := by 
    apply sin_pos_of_pos_of_lt_pi 
    all_goals linarith [Real.pi_pos]

  have h4 : sin (3 * (π / 9)) = 3 * sin (π / 9) - 4 * sin (π / 9) ^ 3 := by 
    rw [sin_three_mul]

  have h5 : cos (3 * (π / 9)) = 4 * cos (π / 9) ^ 3 - 3 * cos (π / 9) := by 
    rw [cos_three_mul]

  have h6 : sin (3 * (π / 9)) = sin (π / 3) := by 
    ring_nf

  have h7 : cos (3 * (π / 9)) = cos (π / 3) := by 
    ring_nf

  have h8 : sin (π / 3) = Real.sqrt 3 / 2 := by 
    rw [sin_pi_div_three]

  have h9 : cos (π / 3) = 1 / 2 := by 
    rw [cos_pi_div_three]

  have eq1 : Real.sqrt 3 / 2 = 3 * sin (π / 9) - 4 * sin (π / 9) ^ 3 := by 
    linarith [h6, h8, h4]

  have eq2 : 1 / 2 = 4 * cos (π / 9) ^ 3 - 3 * cos (π / 9) := by 
    linarith [h7, h9, h5]

  field_simp [h2.ne.symm] at *
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sin_sq_add_cos_sq (π / 9), sq_nonneg (sin (π / 9) - Real.sqrt 3 / 2), sq_nonneg (cos (π / 9) - 1 / 2), sq_nonneg (sin (π / 9) - 1 / 2), eq1, eq2, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]