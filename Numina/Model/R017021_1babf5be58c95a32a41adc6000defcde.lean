import Mathlib

theorem algebra_318017 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : (41 : ℝ)^x = 2009) (h2 : (7 : ℝ)^y = 2009) :
    1 / x + 2 / y = 1 := by

  have h3 : x * (Real.log (41 : ℝ)) = Real.log (2009 : ℝ) := by 
    have h4 : Real.log ((41 : ℝ) ^ x) = Real.log (2009 : ℝ) := by 
      rw [h1]
    have h5 : Real.log ((41 : ℝ) ^ x) = x * Real.log (41 : ℝ) := by 
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h4, h5]

  have h4 : y * (Real.log (7 : ℝ)) = Real.log (2009 : ℝ) := by
    have h6 : Real.log ((7 : ℝ) ^ y) = Real.log (2009 : ℝ) := by
      rw [h2]
    have h7 : Real.log ((7 : ℝ) ^ y) = y * Real.log (7 : ℝ) := by
      rw [Real.log_rpow]
      all_goals linarith
    linarith [h6, h7]

  have h6 : Real.log (2009 : ℝ) = 2 * Real.log (7 : ℝ) + Real.log (41 : ℝ) := by
    have h7 : Real.log (2009 : ℝ) = Real.log ((7 : ℝ) ^ 2 * (41 : ℝ)) := by
      norm_num
    have h8 : Real.log ((7 : ℝ) ^ 2 * (41 : ℝ)) = Real.log ((7 : ℝ) ^ 2) + Real.log (41 : ℝ) := by
      rw [Real.log_mul (by norm_num) (by norm_num)]
    have h9 : Real.log ((7 : ℝ) ^ 2) = 2 * Real.log (7 : ℝ) := by 
      simp [Real.log_pow]
    rw [h7, h8, h9]

  have eq1 : x * Real.log (41 : ℝ) = 2 * Real.log (7 : ℝ) + Real.log (41 : ℝ) := by
    rw [h6] at h3 
    linarith

  have eq2 : y * Real.log (7 : ℝ) = 2 * Real.log (7 : ℝ) + Real.log (41 : ℝ) := by 
    rw [h6] at h4 
    linarith 

  have h7 : Real.log (41 : ℝ) ≠ 0 := by positivity
  have h8 : Real.log (7 : ℝ) ≠ 0 := by positivity

  have hx_eq : x = 1 + 2 * (Real.log (7 : ℝ) / Real.log (41 : ℝ)) := by 
    have h7 : Real.log (41 : ℝ) ≠ 0 := by positivity 
    have h8 : x * Real.log (41 : ℝ) = Real.log (41 : ℝ) + 2 * Real.log (7 : ℝ) := by
      linarith [eq1]
    field_simp at *
    nlinarith

  have hy_eq : y = 2 + (Real.log (41 : ℝ) / Real.log (7 : ℝ)) := by 
    have h7 : Real.log (7 : ℝ) ≠ 0 := by positivity 
    have h8 : y * Real.log (7 : ℝ) = Real.log (41 : ℝ) + 2 * Real.log (7 : ℝ) := by
      linarith [eq2]
    field_simp at *
    nlinarith

  rw [hx_eq, hy_eq]
  field_simp [h7, h8]
  <;> 
  nlinarith [Real.log_pos (show (41 : ℝ) > 1 by norm_num), Real.log_pos (show (7 : ℝ) > 1 by norm_num)]