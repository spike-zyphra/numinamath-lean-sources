import Mathlib

theorem algebra_207149 : (144 : ℝ) ^ ((Real.logb 5 1000) : ℝ) / (10 ^ (6 * (Real.logb 5 12))) = 1 := by
  have h2 : Real.log ( (144 : ℝ) ^ (Real.logb 5 1000) ) = Real.log ( (10 ^ (6 * Real.logb 5 12) ) ) := by
    have h3 : Real.log ( (144 : ℝ) ^ (Real.logb 5 1000) ) = Real.logb 5 1000 * Real.log (144 : ℝ) := by
      rw [Real.log_rpow]
      all_goals linarith
    have h4 : Real.log ( (10 : ℝ) ^ (6 * Real.logb 5 12) ) = 6 * Real.logb 5 12 * Real.log (10 : ℝ) := by
      have h5 : Real.log ( (10 : ℝ) ^ (6 * Real.logb 5 12) ) = (6 * Real.logb 5 12) * Real.log (10 : ℝ) := by
        rw [Real.log_rpow]
        all_goals linarith
      linarith [h5]
    rw [h3, h4]
    have h6 : Real.log (144 : ℝ) = 2 * Real.log (12 : ℝ) := by
      rw [show (144 : ℝ) = (12 : ℝ) ^ 2 by norm_num]
      simp [Real.log_pow]
      all_goals linarith
    rw [h6]
    have h7 : Real.logb 5 1000 = Real.log (1000 : ℝ) / Real.log (5 : ℝ) := by
      field_simp [Real.logb]
    have h8 : Real.logb 5 12 = Real.log (12 : ℝ) / Real.log (5 : ℝ) := by
      field_simp [Real.logb]
    rw [h7, h8]
    have h9 : Real.log (1000 : ℝ) = 3 * Real.log (10 : ℝ) := by
      rw [show (1000 : ℝ) = (10 : ℝ) ^ 3 by norm_num]
      simp [Real.log_pow]
    rw [h9]
    field_simp
    <;> ring
  have h10 : (144 : ℝ) ^ (Real.logb 5 1000) = (10 ^ (6 * Real.logb 5 12) ) := by
    have h11 : Real.log ( (144 : ℝ) ^ (Real.logb 5 1000) ) = Real.log ( (10 ^ (6 * Real.logb 5 12) ) ) := h2
    have h12 : (144 : ℝ) ^ (Real.logb 5 1000) > 0 := by positivity
    have h13 : (10 : ℝ) ^ (6 * Real.logb 5 12) > 0 := by positivity
    have h14 : (144 : ℝ) ^ (Real.logb 5 1000) = (10 : ℝ) ^ (6 * Real.logb 5 12) := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h12) (Set.mem_Ioi.mpr h13) h11
    linarith [h14]
  rw [h10]
  field_simp