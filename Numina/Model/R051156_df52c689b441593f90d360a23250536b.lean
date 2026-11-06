import Mathlib

theorem algebra_2381 : (Real.sqrt 5 - Real.sqrt 7) / (Real.sqrt 5 + Real.sqrt 7) = -6 + Real.sqrt 35 := by
  -- Multiply numerator and denominator by $\sqrt{5} - \sqrt{7}$ to rationalize
  have h1 : (Real.sqrt 5 + Real.sqrt 7) ≠ 0 := by
    have h1 : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)
    have h2 : Real.sqrt 7 > 0 := Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num)
    positivity
  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h4 : Real.sqrt 5 * Real.sqrt 7 = Real.sqrt 35 := by
    calc
      Real.sqrt 5 * Real.sqrt 7 = Real.sqrt (5 * 7 : ℝ) := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt (35 : ℝ) := by norm_num
      _ = Real.sqrt 35 := by norm_num
  field_simp [h1]
  nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 7, Real.sqrt_nonneg 35,
            Real.sq_sqrt (show 0 ≤ (35 : ℝ) by norm_num), Real.mul_self_sqrt (show 0 ≤ (35 : ℝ) by norm_num),
            Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num),
            Real.sqrt_le_sqrt (show (5 : ℝ) ≤ 7 by norm_num), h2, h3, h4]