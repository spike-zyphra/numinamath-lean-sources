import Mathlib

theorem algebra_315730 : 1 / (Real.sqrt 8 + Real.sqrt 11) + 1 / (Real.sqrt 11 + Real.sqrt 14) +
    1 / (Real.sqrt 14 + Real.sqrt 17) + 1 / (Real.sqrt 17 + Real.sqrt 20) +
    1 / (Real.sqrt 20 + Real.sqrt 23) + 1 / (Real.sqrt 23 + Real.sqrt 26) +
    1 / (Real.sqrt 26 + Real.sqrt 29) + 1 / (Real.sqrt 29 + Real.sqrt 32) = 2 * Real.sqrt 2 / 3 := by

  have h1 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h2 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  have h3 : 1 / (Real.sqrt 8 + Real.sqrt 11) = (Real.sqrt 11 - Real.sqrt 8) / 3 := by
    rw [h1]
    have h4 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)
    field_simp [(show Real.sqrt 2 ^ 2 = (2 : ℝ) by norm_num), h4]
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h4 : 1 / (Real.sqrt 11 + Real.sqrt 14) = (Real.sqrt 14 - Real.sqrt 11) / 3 := by
    have h5 : Real.sqrt 14 ^ 2 = 14 := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
    have h6 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)
    field_simp [(show Real.sqrt 11 ^ 2 = (11 : ℝ) by linarith), h5, h6]
    <;> nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sqrt_nonneg (14 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (14 : ℝ) by norm_num)]

  have h5 : 1 / (Real.sqrt 14 + Real.sqrt 17) = (Real.sqrt 17 - Real.sqrt 14) / 3 := by
    have h7 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
    have h8 : Real.sqrt 14 ^ 2 = 14 := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
    field_simp [(show Real.sqrt 14 ^ 2 = (14 : ℝ) by linarith), h7, h8]
    <;> nlinarith [Real.sqrt_nonneg (14 : ℝ), Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (14 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]

  have h6 : 1 / (Real.sqrt 17 + Real.sqrt 20) = (Real.sqrt 20 - Real.sqrt 17) / 3 := by
    have h8 : Real.sqrt 20 ^ 2 = 20 := Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num)
    have h9 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
    field_simp [(show Real.sqrt 17 ^ 2 = (17 : ℝ) by linarith), h8, h9]
    <;> nlinarith [Real.sqrt_nonneg (17 : ℝ), Real.sqrt_nonneg (20 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (20 : ℝ) by norm_num)]

  have h7 : 1 / (Real.sqrt 20 + Real.sqrt 23) = (Real.sqrt 23 - Real.sqrt 20) / 3 := by
    have h10 : Real.sqrt 23 ^ 2 = 23 := Real.sq_sqrt (show (0 : ℝ) ≤ 23 by norm_num)
    have h11 : Real.sqrt 20 ^ 2 = 20 := Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num)
    field_simp [(show Real.sqrt 20 ^ 2 = (20 : ℝ) by linarith), h10, h11]
    <;> nlinarith [Real.sqrt_nonneg (20 : ℝ), Real.sqrt_nonneg (23 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (20 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (23 : ℝ) by norm_num)]

  have h8 : 1 / (Real.sqrt 23 + Real.sqrt 26) = (Real.sqrt 26 - Real.sqrt 23) / 3 := by
    have h12 : Real.sqrt 26 ^ 2 = 26 := Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)
    have h13 : Real.sqrt 23 ^ 2 = 23 := Real.sq_sqrt (show (0 : ℝ) ≤ 23 by norm_num)
    have h14 : Real.sqrt 23 + Real.sqrt 26 ≠ 0 := by
      have h14_1 : Real.sqrt 23 > 0 := by
        positivity
      have h14_2 : Real.sqrt 26 > 0 := by
        positivity
      linarith
    field_simp [h12, h13, h14]
    <;> nlinarith [Real.sqrt_nonneg (23 : ℝ), Real.sqrt_nonneg (26 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (23 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (26 : ℝ) by norm_num)]

  have h9 : 1 / (Real.sqrt 26 + Real.sqrt 29) = (Real.sqrt 29 - Real.sqrt 26) / 3 := by
    have h14 : Real.sqrt 29 ^ 2 = 29 := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
    have h15 : Real.sqrt 26 ^ 2 = 26 := Real.sq_sqrt (show (0 : ℝ) ≤ 26 by norm_num)
    have h16 : Real.sqrt 26 + Real.sqrt 29 ≠ 0 := by
      have h16_1 : Real.sqrt 26 > 0 := by
        positivity
      have h16_2 : Real.sqrt 29 > 0 := by
        positivity
      linarith
    field_simp [h14, h15, h16]
    <;> nlinarith [Real.sqrt_nonneg (26 : ℝ), Real.sqrt_nonneg (29 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (26 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (29 : ℝ) by norm_num)]

  have h10 : 1 / (Real.sqrt 29 + Real.sqrt 32) = (Real.sqrt 32 - Real.sqrt 29) / 3 := by
    have h17 : Real.sqrt 32 ^ 2 = 32 := Real.sq_sqrt (show (0 : ℝ) ≤ 32 by norm_num)
    have h18 : Real.sqrt 29 ^ 2 = 29 := Real.sq_sqrt (show (0 : ℝ) ≤ 29 by norm_num)
    have h19 : Real.sqrt 29 + Real.sqrt 32 ≠ 0 := by
      have h19_1 : Real.sqrt 29 > 0 := by
        positivity
      have h19_2 : Real.sqrt 32 > 0 := by
        positivity
      linarith
    field_simp [h17, h18, h19]
    <;> nlinarith [Real.sqrt_nonneg (29 : ℝ), Real.sqrt_nonneg (32 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (29 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num)]

  rw [h3, h4, h5, h6, h7, h8, h9, h10]
  rw [h1, h2]
  ring_nf