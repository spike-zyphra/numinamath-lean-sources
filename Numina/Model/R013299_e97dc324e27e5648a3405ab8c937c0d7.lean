import Mathlib

theorem algebra_317946 : round ((Real.sqrt 2 + 1) / (Real.sqrt 2 - 1) - (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1) : ℝ) = 6 := by
  have h1 : Real.sqrt 2 > 0 := by
    positivity
  have h2 : Real.sqrt 2 - 1 > 0 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h3 : (Real.sqrt 2 + 1 : ℝ) / (Real.sqrt 2 - 1) = (Real.sqrt 2 + 1) ^ 2 := by
    field_simp [(show (Real.sqrt 2 - 1 : ℝ) ≠ 0 by linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), h1, h2])]
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h4 : (Real.sqrt 2 - 1 : ℝ) / (Real.sqrt 2 + 1) = (Real.sqrt 2 - 1) ^ 2 := by
    field_simp [(show (Real.sqrt 2 + 1 : ℝ) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ)]
    )]
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h5 : (Real.sqrt 2 + 1 : ℝ) / (Real.sqrt 2 - 1) - (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1) = 4 * Real.sqrt 2 := by
    rw [h3, h4]
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  rw [h5]
  rw [round_eq]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> try
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num))]