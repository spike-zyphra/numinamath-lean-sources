import Mathlib

theorem algebra_2102 : Real.sqrt (3 + 2 * Real.sqrt 2) + Real.sqrt (3 - 2 * Real.sqrt 2) = 2 * Real.sqrt 2 := by
  have h1 : Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt 2 + 1 := by
    have h2 : (Real.sqrt 2 + 1) ^ 2 = 3 + 2 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
    have h3 : Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt ((Real.sqrt 2 + 1) ^ 2) := by
      rw [h2]
    rw [h3]
    rw [Real.sqrt_sq (by positivity)]
  
  have h4 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
    have h5 : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
    have h6 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt ((Real.sqrt 2 - 1) ^ 2) := by
      rw [h5]
    rw [h6]
    rw [Real.sqrt_sq (by
      have h7 : Real.sqrt 2 ≥ 1 := by
        have h8 : Real.sqrt 1 = 1 := Real.sqrt_one
        have h9 : Real.sqrt 2 ≥ Real.sqrt 1 := by
          apply Real.sqrt_le_sqrt
          norm_num
        rw [h8] at h9
        linarith
      nlinarith [Real.sqrt_nonneg 2]
    )]
  
  rw [h1, h4]
  ring