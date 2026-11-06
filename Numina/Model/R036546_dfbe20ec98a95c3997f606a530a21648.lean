import Mathlib

open Real

theorem algebra_13515 : (sin (50 * π / 180) ^ 4 + cos (50 * π / 180) ^ 2 + sin (75 * π / 180)) / (cos (50 * π / 180) ^ 4 + sin (50 * π / 180) ^ 2 + cos (15 * π / 180)) = 1 := by
  have h1 : sin (75 * π / 180) = cos (15 * π / 180) := by 
    have h2 : 75 * π / 180 = π / 2 - 15 * π / 180 := by 
      linarith [pi_pos]
    rw [h2]
    rw [sin_pi_div_two_sub]
  have h3 : sin (50 * π / 180) ^ 4 + cos (50 * π / 180) ^ 2 = cos (50 * π / 180) ^ 4 + sin (50 * π / 180) ^ 2 := by
    have h4 : sin (50 * π / 180) ^ 2 + cos (50 * π / 180) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (50 * π / 180)
    have h5 : sin (50 * π / 180) ^ 4 = (sin (50 * π / 180) ^ 2) ^ 2 := by ring
    have h6 : cos (50 * π / 180) ^ 4 = (cos (50 * π / 180) ^ 2) ^ 2 := by ring
    rw [h5, h6]
    have h7 : sin (50 * π / 180) ^ 2 = 1 - cos (50 * π / 180) ^ 2 := by 
      linarith [h4]
    have h8 : cos (50 * π / 180) ^ 2 = 1 - sin (50 * π / 180) ^ 2 := by 
      linarith [h4]
    rw [h7, h8]
    all_goals nlinarith 
  have eq1 : sin (50 * π / 180) ^ 4 + cos (50 * π / 180) ^ 2 + sin (75 * π / 180) = cos (50 * π / 180) ^ 4 + sin (50 * π / 180) ^ 2 + cos (15 * π / 180) := by 
    rw [h1]
    linarith [h3]
  -- Substitute the equality into the main goal
  rw [eq1]
  -- Use set to handle the denominator expression
  set denom := cos (50 * π / 180) ^ 4 + sin (50 * π / 180) ^ 2 + cos (15 * π / 180)
  have h_denom_pos : 0 < denom := by
    have h50_pos : 0 < sin (50 * π / 180) := by
      have h1 : 0 < 50 * π / 180 := by linarith [pi_pos]
      have h2 : sin (50 * π / 180) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        linarith [pi_pos]
        linarith [pi_pos]
      linarith
    have h50cos_pos : 0 < cos (50 * π / 180) := by
      have h1 : 0 < 50 * π / 180 := by linarith [pi_pos]
      have h2 : cos (50 * π / 180) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [pi_pos]
        linarith [pi_pos]
      linarith
    have h15cos_pos : 0 < cos (15 * π / 180) := by
      have h1 : 0 < 15 * π / 180 := by linarith [pi_pos]
      have h2 : cos (15 * π / 180) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [pi_pos]
        linarith [pi_pos]
      linarith
    positivity
  -- Now that we have h_denom_pos, we can prove the main goal
  field_simp [show denom ≠ 0 by linarith [h_denom_pos]]
  all_goals nlinarith [Real.sin_sq_add_cos_sq (50 * π / 180), Real.sin_sq_add_cos_sq (15 * π / 180), sq_nonneg (sin (50 * π / 180) * cos (50 * π / 180)), sq_nonneg (sin (15 * π / 180) * cos (15 * π / 180)), sq_pos_of_pos h50_pos, sq_pos_of_pos h50cos_pos, sq_pos_of_pos h15cos_pos]