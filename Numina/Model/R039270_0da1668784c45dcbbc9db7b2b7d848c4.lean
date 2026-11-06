import Mathlib

theorem algebra_148117 (m : ℝ) (hm : m < 0) (h : (1 / 2) * (1 / 5) * (2 * m ^ 2) = 242) :
    m = -11 * Real.sqrt 10 := by
  have eq1 : m ^ 2 = 1210 := by
    nlinarith 
  have eq2 : m = -Real.sqrt 1210 := by
    have h3 : m ^ 2 = (1210 : ℝ) := eq1
    have h4 : Real.sqrt (m ^ 2) = Real.sqrt (1210 : ℝ) := by
      rw [h3]
    have h5 : Real.sqrt (m^2) = -m := by 
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_neg hm]
      all_goals linarith 
    have h6 : -m = Real.sqrt (1210 : ℝ) := by
      linarith [h4, h5]
    have h7 : m = -Real.sqrt (1210 : ℝ) := by 
      linarith 
    exact h7
  have eq3 : Real.sqrt (1210 : ℝ) = 11 * Real.sqrt 10 := by
    have h3 : (Real.sqrt (1210 : ℝ)) ^ 2 = (11 * Real.sqrt 10) ^ 2 := by
      have h4 : (Real.sqrt (1210 : ℝ)) ^ 2 = (1210 : ℝ) := by
        rw [Real.sq_sqrt]
        all_goals nlinarith 
      have h5 : (11 * Real.sqrt 10) ^ 2 = (1210 : ℝ) := by 
        calc
          (11 * Real.sqrt 10) ^ 2 = (11 : ℝ) ^ 2 * (Real.sqrt 10) ^2 := by ring 
          _ = (121 : ℝ) * (10 : ℝ) := by 
            have h6 : (Real.sqrt 10) ^2 = 10 := Real.sq_sqrt (by norm_num)
            rw [h6]
            all_goals norm_num 
          _ = (1210 : ℝ) := by norm_num 
      linarith [h4, h5]
    have h4 : 0 ≤ (Real.sqrt (1210 : ℝ) : ℝ) := by positivity
    have h5 : 0 ≤ (11 * Real.sqrt 10 : ℝ) := by positivity
    have h2 : Real.sqrt (1210 : ℝ) = 11 * Real.sqrt 10 := by
      nlinarith [h3, h4, h5, Real.sqrt_nonneg 1210]
    exact h2
  rw [eq3] at eq2 
  linarith