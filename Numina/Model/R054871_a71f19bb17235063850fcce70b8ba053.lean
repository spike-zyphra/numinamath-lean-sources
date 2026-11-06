import Mathlib

theorem algebra_96256 : Real.sqrt (3 + 2 * Real.sqrt 2) - Real.sqrt (3 - 2 * Real.sqrt 2) = 2 := by
  have h1 : Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt 2 + 1 := by
    have h2 : 0 ≤ Real.sqrt 2 + 1 := by
      have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      linarith
    have h4 : (Real.sqrt 2 + 1) ^ 2 = 3 + 2 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 from by norm_num), Real.sqrt_nonneg 2]
    rw [← h4]
    field_simp [Real.sqrt_sq h2]
    all_goals nlinarith

  have h5 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
    have h8 : Real.sqrt 2 - 1 > 0 := by
      have h9 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith
    have h6 : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 from by norm_num), Real.sqrt_nonneg 2]
    have h7 : 0 ≤ Real.sqrt 2 - 1 := by linarith [show 1 < Real.sqrt 2 from Real.lt_sqrt_of_sq_lt (by norm_num)]
    rw [← h6]
    field_simp [Real.sqrt_sq h7]
    all_goals nlinarith
  
  rw [h1, h5]
  nlinarith