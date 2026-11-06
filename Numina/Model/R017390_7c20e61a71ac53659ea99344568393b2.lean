import Mathlib

theorem algebra_320879 : (2 * Real.sqrt 6 / (Real.sqrt 3 + Real.sqrt 2 - Real.sqrt 5)) = Real.sqrt 3 + Real.sqrt 2 + Real.sqrt 5 := by
  have h1 : Real.sqrt 3 + Real.sqrt 2 - Real.sqrt 5 ≠ 0 := by
    by_contra h
    have h2 : Real.sqrt 3 + Real.sqrt 2 = Real.sqrt 5 := by
      nlinarith [h]
    have h3 : (Real.sqrt 3 + Real.sqrt 2) ^ 2 = (Real.sqrt 5) ^ 2 := by
      rw [h2]
    have h4 : (Real.sqrt 3 + Real.sqrt 2) ^ 2 = Real.sqrt 3 ^ 2 + Real.sqrt 2 ^ 2 + 2 * (Real.sqrt 3 * Real.sqrt 2) := by ring
    have h5 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h7 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [h4] at h3
    rw [h5, h6] at h3
    rw [h7] at h3
    have h8 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
      calc
        Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * (2 : ℝ)) := by
          rw [← Real.sqrt_mul (by linarith)]
        _ = Real.sqrt (6 : ℝ) := by
          norm_num
    rw [h8] at h3
    nlinarith [Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num : (6 : ℝ) > 0), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num : (6 : ℝ) ≥ 0)]
  have h2 : Real.sqrt 6 = Real.sqrt 3 * Real.sqrt 2 := by
    calc
      Real.sqrt 6 = Real.sqrt (3 * 2 : ℝ) := by
        norm_num
      _ = Real.sqrt (3 : ℝ) * Real.sqrt (2 : ℝ) := by
        rw [Real.sqrt_mul (by linarith)]
      _ = Real.sqrt 3 * Real.sqrt 2 := by
        ring
  field_simp [h1]
  nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, 
          Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num : (3 : ℝ) ≥ 0), 
          Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num : (2 : ℝ) ≥ 0), 
          Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num : (5 : ℝ) ≥ 0), 
          Real.sqrt_nonneg 6, 
          Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num : (6 : ℝ) ≥ 0), 
          mul_pos (Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num : (3 : ℝ) > 0)) 
            (Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0)), 
          mul_pos (Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num : (3 : ℝ) > 0)) 
            (Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0)), 
          mul_pos (Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0)) 
            (Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0)), 
          h2, 
          mul_pos (Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num : (3 : ℝ) > 0)) 
            (Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0))
        ]