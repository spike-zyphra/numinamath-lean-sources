import Mathlib

open Real

theorem algebra_7281 : √(5 - 2 * √6) = √3 - √2 := by
  have h1 : (√3 - √2) ^ 2 = 5 - 2 * √6 := by
    have h2 : (√3 - √2) ^ 2 = (√3) ^ 2 + (√2) ^ 2 - 2 * (√3 * √2) := by
      ring
    rw [h2]
    have h3 : (√3 : ℝ) ^ 2 = 3 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    have h4 : (√2 : ℝ) ^ 2 = 2 := by
      exact Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    have h5 : √3 * √2 = √6 := by
      rw [← Real.sqrt_mul (by norm_num)]
      all_goals norm_num
    rw [h3, h4, h5]
    <;> ring_nf <;> norm_num
    <;> ring
  have h2 : 0 ≤ (5 - 2 * √6 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg (3), Real.sqrt_nonneg (2), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  have h3 : 0 ≤ (√3 - √2 : ℝ) := by
    have h4 : √3 > √2 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    nlinarith [Real.sqrt_nonneg (3), Real.sqrt_nonneg (2)]
  rw [← h1]
  rw [Real.sqrt_sq (h3)]
  all_goals norm_num [Real.sqrt_nonneg, h2, h3]
  all_goals linarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 3, Real.sqrt_nonneg 2]