import Mathlib

theorem algebra_20339 : Real.logb (Real.sqrt 5) (125 * Real.sqrt 5) = 7 := by
  have h1 : Real.logb (Real.sqrt 5) (125 * Real.sqrt 5) = Real.log (125 * Real.sqrt 5) / Real.log (Real.sqrt 5) := by
    field_simp [Real.logb]

  have h2 : Real.log (125 * Real.sqrt 5) = Real.log 125 + Real.log (Real.sqrt 5) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  
  have h3 : Real.log 125 = 3 * Real.log 5 := by
    have h4 : (125 : ℝ) = 5 ^ 3 := by norm_num
    rw [h4]
    simp [Real.log_pow]

  have h5 : Real.log (Real.sqrt 5) = (1 / 2) * Real.log 5 := by
    have h6 : Real.sqrt 5 = (5 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h6]
    simp [Real.log_rpow]

  have h7 : Real.log (125 * Real.sqrt 5) = 7 / 2 * Real.log 5 := by 
    rw [h2, h3, h5]
    all_goals linarith

  have h8 : Real.log (Real.sqrt 5) = (1 / 2) * Real.log 5 := h5
  
  rw [h1, h7, h8]

  have h9 : Real.log 5 ≠ 0 := by
    linarith [Real.log_pos (show (5 : ℝ) > 1 by norm_num)]

  field_simp [h9]
  <;> ring