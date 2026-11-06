import Mathlib

theorem algebra_228827 : Real.logb 20 80 < Real.logb 80 640 := by
  have h1 : Real.logb 20 80 = Real.log 80 / Real.log 20 := by
    field_simp [Real.logb]
  have h2 : Real.logb 80 640 = Real.log 640 / Real.log 80 := by
    field_simp [Real.logb]
  rw [h1, h2]
  have h3 : Real.log 20 > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h4 : Real.log 80 > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h5 : Real.log 640 > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h6 : Real.log 80 ^ 2 < Real.log 20 * Real.log 640 := by
    have h7 : Real.log 80 = 4 * Real.log 2 + Real.log 5 := by
      calc
        Real.log 80 = Real.log (2 ^ 4 * 5) := by norm_num
        _ = Real.log (2 ^ 4) + Real.log 5 := by rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = 4 * Real.log 2 + Real.log 5 := by simp [Real.log_pow]
    have h8 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
      calc
        Real.log 20 = Real.log (2 ^ 2 * 5) := by norm_num
        _ = Real.log (2 ^ 2) + Real.log 5 := by rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = 2 * Real.log 2 + Real.log 5 := by simp [Real.log_pow]
    have h9 : Real.log 640 = 7 * Real.log 2 + Real.log 5 := by
      calc
        Real.log 640 = Real.log (2 ^ 7 * 5) := by norm_num
        _ = Real.log (2 ^ 7) + Real.log 5 := by rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = 7 * Real.log 2 + Real.log 5 := by simp [Real.log_pow]
    rw [h7, h8, h9]
    have h10 : Real.log 5 > 2 * Real.log 2 := by
      have h11 : Real.log 5 > Real.log 4 := by
        apply Real.log_lt_log
        all_goals norm_num
      have h12 : Real.log 4 = 2 * Real.log 2 := by
        calc
          Real.log 4 = Real.log (2 ^ 2) := by norm_num
          _ = 2 * Real.log 2 := by simp [Real.log_pow]
      linarith [h11, h12]
    have h13 : Real.log 2 > 0 := by
      apply Real.log_pos
      all_goals norm_num
    nlinarith [h10, Real.log_pos (show (2 : ℝ) > 1 by norm_num), Real.log_pos (show (5 : ℝ) > 1 by norm_num)]
  have h7 : Real.log 80 / Real.log 20 < Real.log 640 / Real.log 80 := by
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h6, Real.log_pos (show (20 : ℝ) > 1 by norm_num), Real.log_pos (show (80 : ℝ) > 1 by norm_num)]
  linarith