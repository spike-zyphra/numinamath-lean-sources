import Mathlib

theorem algebra_284904 : 1 / Real.logb 2 (12 * Real.sqrt 5) +
    1 / Real.logb 3 (12 * Real.sqrt 5) +
    1 / Real.logb 4 (12 * Real.sqrt 5) +
    1 / Real.logb 5 (12 * Real.sqrt 5) +
    1 / Real.logb 6 (12 * Real.sqrt 5) = 2 := by

  have h1 : Real.sqrt 5 > 0 := by positivity
  have h2 : Real.sqrt 5 > 0 := by positivity
  have h3 : 12 * Real.sqrt 5 > 0 := by positivity
  have h4 : Real.logb 2 (12 * Real.sqrt 5) = Real.log (12 * Real.sqrt 5) / Real.log (2 : ℝ) := by
    field_simp [Real.logb]
  have h5 : Real.logb 3 (12 * Real.sqrt 5) = Real.log (12 * Real.sqrt 5) / Real.log (3 : ℝ) := by
    field_simp [Real.logb]
  have h6 : Real.logb 4 (12 * Real.sqrt 5) = Real.log (12 * Real.sqrt 5) / Real.log (4 : ℝ) := by
    field_simp [Real.logb]
  have h7 : Real.logb 5 (12 * Real.sqrt 5) = Real.log (12 * Real.sqrt 5) / Real.log (5 : ℝ) := by
    field_simp [Real.logb]
  have h8 : Real.logb 6 (12 * Real.sqrt 5) = Real.log (12 * Real.sqrt 5) / Real.log (6 : ℝ) := by
    field_simp [Real.logb]

  rw [h4, h5, h6, h7, h8]

  have h51 : Real.log (12 * Real.sqrt 5) = Real.log (12 : ℝ) + Real.log (Real.sqrt 5 : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity)]

  have h52 : Real.log (12 : ℝ) = 2 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
    calc 
      Real.log (12 : ℝ) = Real.log ((2 ^ 2 * 3 : ℝ) ) := by norm_num
      _ = Real.log ((2 ^ 2 : ℝ)) + Real.log (3 : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = 2 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
        have h100 : Real.log ((2 ^ 2 : ℝ)) = 2 * Real.log (2 : ℝ) := by
          simp [Real.log_pow]
        rw [h100]

  have h53 : Real.log (Real.sqrt 5 : ℝ) = (1 / 2) * Real.log (5 : ℝ) := by
    have h100 : Real.sqrt 5 = (5 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h100]
    simp [Real.log_rpow]
  have h54 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by 
    calc 
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log (2 : ℝ) := by 
        simp [Real.log_pow]

  have h55 : Real.log (6 : ℝ) = Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
    calc 
      Real.log (6 : ℝ) = Real.log ((2 * 3 : ℝ) ) := by norm_num
      _ = Real.log (2 : ℝ) + Real.log (3 : ℝ) := by 
        rw [Real.log_mul (by positivity) (by positivity)]

  have h56 : Real.log (12 * Real.sqrt 5) = 2 * Real.log (2 : ℝ) + Real.log (3 : ℝ) + (1 / 2) * Real.log (5 : ℝ) := by
    rw [h51, h52, h53]
    all_goals ring

  have h17 : Real.log (12 * Real.sqrt 5) = 2 * Real.log (2 : ℝ) + Real.log (3 : ℝ) + (1 / 2) * Real.log (5 : ℝ) := h56
  have h18 : Real.log (12 * Real.sqrt 5) ≠ 0 := by
    have h19 : Real.log (12 * Real.sqrt 5) > 0 := by
      have h20 : 12 * Real.sqrt 5 > 1 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
      have h21 : Real.log (12 * Real.sqrt 5) > Real.log (1 : ℝ) := by
        apply Real.log_lt_log
        all_goals nlinarith
      have h22 : Real.log (1 : ℝ) = 0 := by
        simp [Real.log_one]
      linarith
    linarith

  have h57 : Real.log (2 : ℝ) ≠ 0 := by positivity
  have h58 : Real.log (3 : ℝ) ≠ 0 := by positivity
  have h59 : Real.log (5 : ℝ) ≠ 0 := by positivity

  field_simp [h56, h18, h57, h58, h59, Real.sq_sqrt]
  nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]