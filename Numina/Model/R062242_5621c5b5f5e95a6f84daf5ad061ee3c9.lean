import Mathlib

theorem algebra_22420 : Real.logb 2 3 * Real.logb 3 4 * Real.logb 4 5 * Real.logb 5 6 * Real.logb 6 7 * Real.logb 7 8 = 3 := by
  have h1 : Real.logb 2 3 = Real.log 3 / Real.log 2 := by
    field_simp [Real.logb]
  have h2 : Real.logb 3 4 = Real.log 4 / Real.log 3 := by
    field_simp [Real.logb]
  have h3 : Real.logb 4 5 = Real.log 5 / Real.log 4 := by
    field_simp [Real.logb]
  have h4 : Real.logb 5 6 = Real.log 6 / Real.log 5 := by
    field_simp [Real.logb]
  have h5 : Real.logb 6 7 = Real.log 7 / Real.log 6 := by
    field_simp [Real.logb]
  have h6 : Real.logb 7 8 = Real.log 8 / Real.log 7 := by
    field_simp [Real.logb]
  rw [h1, h2, h3, h4, h5, h6]
  have h7 : Real.log 4 = 2 * Real.log 2 := by
    rw [show Real.log 4 = Real.log (2^2) by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show Real.log 8 = Real.log (2^3) by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  -- Replace Real.log 4 and Real.log 8 with their expressions in terms of Real.log 2
  rw [h7, h8]
  -- The product telescopes to 3
  field_simp [h7, h8]
  <;> ring_nf <;> field_simp <;> ring
  all_goals linarith