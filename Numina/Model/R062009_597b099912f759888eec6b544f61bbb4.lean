import Mathlib

theorem algebra_14877 (q : ℝ) (h : q > 0) (h' : 15 = 3 * q^2 / (2 * Real.sqrt 3)) :
    15 + q^2 / (Real.sqrt 3) = 25 := by
        have h1 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
        have h2 : q^2 = 10 * Real.sqrt 3 := by
            field_simp [h1] at h'
            nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        have h3 : q^2 / Real.sqrt 3 = 10 := by
            have h4 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
            have h5 : q^2 = 10 * Real.sqrt 3 := by
                field_simp [h4] at h'
                nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
            have h6 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
            field_simp [h6]
            nlinarith
        linarith [h3]