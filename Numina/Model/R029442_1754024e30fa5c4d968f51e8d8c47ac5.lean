import Mathlib

theorem algebra_218956 : 1 / (Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 5) = (Real.sqrt 6 * (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5)) / 12 := by
  have h1 : Real.sqrt 2 > 0 := by positivity
  have h2 : Real.sqrt 3 > 0 := by positivity
  have h3 : Real.sqrt 5 > 0 := by positivity

  have h4 : Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 5 ≠ 0 := by
    by_contra h
    have h5 : Real.sqrt 2 + Real.sqrt 3 = Real.sqrt 5 := by linarith
    have h6 : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = (Real.sqrt 5) ^ 2 := by
      rw [h5]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3]

  have h5 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    have h6 : Real.sqrt 6 = Real.sqrt (2 * 3) := by
      norm_num
    rw [h6]
    rw [Real.sqrt_mul (by norm_num)]
    all_goals norm_num

  rw [h5]
  field_simp [(show Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 5 ≠ 0 by exact h4)]
  <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, sq_nonneg (Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 5), sq_nonneg (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5), sq_nonneg (Real.sqrt 2 - Real.sqrt 3), sq_nonneg (Real.sqrt 2 - Real.sqrt 5), sq_nonneg (Real.sqrt 3 - Real.sqrt 5), mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3]