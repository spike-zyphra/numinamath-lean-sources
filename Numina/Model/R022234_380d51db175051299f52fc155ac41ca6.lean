import Mathlib

theorem algebra_9576 : Real.sqrt (28 + Real.sqrt 748) = Real.sqrt 11 + Real.sqrt 17 := by
  have h1 : (Real.sqrt 11 + Real.sqrt 17) ^ 2 = 28 + Real.sqrt 748 := by
    have h2 : (Real.sqrt 11 + Real.sqrt 17) ^ 2 = (Real.sqrt 11) ^ 2 + (Real.sqrt 17) ^ 2 + 2 * (Real.sqrt 11 * Real.sqrt 17) := by
      ring
    rw [h2]
    have h3 : (Real.sqrt 11) ^ 2 = 11 := Real.sq_sqrt (by norm_num)
    have h4 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    rw [h3, h4]
    have h5 : Real.sqrt 11 * Real.sqrt 17 = Real.sqrt 187 := by
      rw [← Real.sqrt_mul (by norm_num)]
      norm_num
    have h6 : 2 * (Real.sqrt 11 * Real.sqrt 17) = Real.sqrt 748 := by
      rw [h5]
      have h7 : Real.sqrt 748 = 2 * Real.sqrt 187 := by
        have h8 : (2 * Real.sqrt 187) ^ 2 = (748 : ℝ) := by
          calc
            (2 * Real.sqrt 187) ^ 2 = 4 * (Real.sqrt 187) ^ 2 := by ring
            _ = 4 * (187 : ℝ) := by
              rw [Real.sq_sqrt]
              all_goals norm_num
            _ = (748 : ℝ) := by
              norm_num
        have h9 : (2 * Real.sqrt 187) ≥ 0 := by
          positivity
        have h10 : Real.sqrt 748 = 2 * Real.sqrt 187 := by
          rw [← h8]
          field_simp [Real.sqrt_eq_iff_sq_eq]
        linarith [h10]
      linarith [h7]
    linarith [h6]
  have h5 : Real.sqrt (28 + Real.sqrt 748) = Real.sqrt ((Real.sqrt 11 + Real.sqrt 17) ^ 2) := by
    rw [h1]
  have h6 : Real.sqrt ((Real.sqrt 11 + Real.sqrt 17) ^ 2) = Real.sqrt 11 + Real.sqrt 17 := by
    rw [Real.sqrt_sq (by positivity)]
  rw [h5, h6]