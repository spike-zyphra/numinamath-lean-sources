import Mathlib

theorem algebra_106982 : 4 + Real.sqrt (Real.logb 3 18171) > Real.logb 3 2019 := by
  have h1 : Real.logb 3 18171 = 2 + Real.logb 3 2019 := by
    calc
      Real.logb 3 18171 = Real.logb 3 (3^2 * 2019) := by norm_num
      _ = Real.logb 3 (3^2) + Real.logb 3 2019 := by rw [Real.logb_mul (by norm_num) (by norm_num)]
      _ = Real.logb 3 (3^2) + Real.logb 3 2019 := by rfl
      _ = (2 : ℝ) + Real.logb 3 2019 := by
        have h4 : Real.logb 3 (3^2 : ℝ) = (2 : ℝ) := by
          simp [Real.logb_pow]
        rw [h4]
        all_goals norm_num
      _ = 2 + Real.logb 3 2019 := by ring
  rw [h1]
  have h2 : Real.logb 3 2019 < (7 : ℝ) := by
    have h3 : Real.logb 3 2019 < Real.logb 3 (2187 : ℝ) := by
      apply Real.logb_lt_logb
      all_goals norm_num
    have h4 : Real.logb 3 (2187 : ℝ) = 7 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith
  have h20 : Real.logb 3 2019 > 0 := by
    apply Real.logb_pos
    all_goals norm_num
  nlinarith [Real.sqrt_nonneg (2 + Real.logb 3 2019), Real.sq_sqrt (show 2 + Real.logb 3 2019 ≥ 0 by linarith), Real.sqrt_nonneg (2 + Real.logb 3 2019), sq_nonneg (Real.sqrt (2 + Real.logb 3 2019) - 3), sq_nonneg (Real.logb 3 2019 - 4), Real.sqrt_nonneg (2 + Real.logb 3 2019)]