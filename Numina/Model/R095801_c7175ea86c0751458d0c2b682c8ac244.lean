import Mathlib

open Real

theorem algebra_99650 {x : ℝ} (hx : x = 13 / sqrt (19 + 8 * sqrt 3)) :
    ((x^4 - 6 * x^3 - 2 * x^2 + 18 * x + 23) / (x^2 - 8 * x + 15)) = 5 := by
  have h1 : sqrt (19 + 8 * sqrt 3) = 4 + Real.sqrt 3 := by
    have h2 : (4 + Real.sqrt 3) ^ 2 = 19 + 8 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
    have h3 : 0 ≤ 19 + 8 * Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3]
    have h4 : 0 ≤ (4 + Real.sqrt 3) := by linarith [Real.sqrt_nonneg 3]
    rw [← h2]
    field_simp [Real.sqrt_sq h4, h3]
  have h5 : x = 4 - Real.sqrt 3 := by
    rw [hx, h1]
    have h6 : (13 : ℝ) / (4 + Real.sqrt 3) = 4 - Real.sqrt 3 := by
      have denom : (4 + Real.sqrt 3) ≠ 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
      field_simp [denom]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    linarith [h6]
  rw [h5]
  have h6 : (4 - Real.sqrt 3 : ℝ) ^ 2 - 8 * (4 - Real.sqrt 3 : ℝ) + 15 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h7 : (4 - Real.sqrt 3 : ℝ) ^ 4 - 6 * (4 - Real.sqrt 3 : ℝ) ^ 3 - 2 * (4 - Real.sqrt 3 : ℝ) ^ 2 + 18 * (4 - Real.sqrt 3 : ℝ) + 23 = 10 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), pow_two (Real.sqrt 3), pow_three (Real.sqrt 3), pow_two (4 - Real.sqrt 3), pow_three (4 - Real.sqrt 3)]
  have h8 : (4 - Real.sqrt 3 : ℝ) ^ 2 - 8 * (4 - Real.sqrt 3 : ℝ) + 15 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  field_simp [h6, h7, h8]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]