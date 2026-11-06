import Mathlib

open Real

theorem algebra_70150 {x : ℝ} (hx : x = (sqrt (6 + 2 * sqrt 5) + sqrt (6 - 2 * sqrt 5)) / sqrt 20) :
    (1 + x^5 - x^7)^(2012^(3^11)) = 1 := by
  have h1 : sqrt (6 + 2 * sqrt 5) = sqrt 5 + 1 := by
    have h2 : (sqrt 5 + 1) ^ 2 = 6 + 2 * sqrt 5 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [← h2]
    field_simp
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h4 : sqrt (6 - 2 * sqrt 5) = sqrt 5 - 1 := by
    have h5 : (sqrt 5 - 1) ^ 2 = 6 - 2 * sqrt 5 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [← h5]
    have : 0 ≤ sqrt 5 - 1 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [Real.sqrt_sq (by nlinarith)]
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h7 : sqrt 20 = 2 * sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have hx1 : x = 1 := by
    rw [hx]
    rw [h1, h4, h7]
    field_simp
    all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  rw [hx1]
  norm_num