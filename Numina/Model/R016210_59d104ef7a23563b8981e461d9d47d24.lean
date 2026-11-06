import Mathlib

theorem algebra_11284 : Real.logb (Real.sqrt 6) (216 * Real.sqrt 6) = 7 := by
  have h1 : Real.logb (Real.sqrt 6) (216 * Real.sqrt 6) = (Real.log (216 * Real.sqrt 6) ) / (Real.log (Real.sqrt 6) ) := by
    field_simp [Real.logb]
  rw [h1]
  have h2 : Real.log (216 * Real.sqrt 6) = Real.log (216) + Real.log (Real.sqrt 6) := by
    rw [Real.log_mul (by positivity) (by positivity)]
  have h3 : Real.log (216 : ℝ) = 3 * Real.log (6 : ℝ) := by
    rw [show (216 : ℝ) = (6 : ℝ) ^ 3 by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  have h4 : Real.log (Real.sqrt 6) = (1 / 2 : ℝ) * Real.log (6 : ℝ) := by
    have h5 : Real.sqrt 6 = (6 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h5]
    have h6 : Real.log ((6 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.log (6 : ℝ) := by
      rw [Real.log_rpow]
      all_goals norm_num
      all_goals linarith
    linarith
  rw [h2, h3, h4]
  have h7 : Real.log (6 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals norm_num
    all_goals linarith
  field_simp [h7]
  <;> ring
  <;> norm_num
  all_goals linarith
  all_goals norm_num
  all_goals linarith
  all_goals norm_num