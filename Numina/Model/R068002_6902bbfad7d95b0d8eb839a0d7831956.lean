import Mathlib

theorem algebra_57819 : Real.sqrt (10 + Real.sqrt 24 + Real.sqrt 40 + Real.sqrt 60) = Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 := by
  have h1 : Real.sqrt 24 = 2 * Real.sqrt 2 * Real.sqrt 3 := by
    have h1 : Real.sqrt 24 = Real.sqrt (4 * 6) := by norm_num
    rw [h1]
    have h2 : Real.sqrt (4 * 6) = Real.sqrt 4 * Real.sqrt 6 := by
      rw [Real.sqrt_mul]
      all_goals norm_num
    rw [h2]
    have h3 : Real.sqrt 4 = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      have h4 : Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
      rw [h4]
      rw [Real.sqrt_mul]
      all_goals norm_num
    rw [h3, h4]
    <;> ring_nf <;> norm_num
  have h2 : Real.sqrt 40 = 2 * Real.sqrt 2 * Real.sqrt 5 := by
    have h1 : Real.sqrt 40 = Real.sqrt (4 * 10) := by norm_num
    rw [h1]
    have h2 : Real.sqrt (4 * 10) = Real.sqrt 4 * Real.sqrt 10 := by
      rw [Real.sqrt_mul]
      all_goals norm_num
    rw [h2]
    have h3 : Real.sqrt 4 = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : Real.sqrt 10 = Real.sqrt 2 * Real.sqrt 5 := by
      have h4 : Real.sqrt 10 = Real.sqrt (2 * 5) := by norm_num
      rw [h4]
      rw [Real.sqrt_mul]
      all_goals norm_num
    rw [h3, h4]
    <;> ring_nf <;> norm_num
  have h3 : Real.sqrt 60 = 2 * Real.sqrt 3 * Real.sqrt 5 := by
    have h1 : Real.sqrt 60 = Real.sqrt (4 * 15) := by norm_num
    rw [h1]
    have h2 : Real.sqrt (4 * 15) = Real.sqrt 4 * Real.sqrt 15 := by
      rw [Real.sqrt_mul]
      all_goals norm_num
    rw [h2]
    have h3 : Real.sqrt 4 = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 := by
      have h4 : Real.sqrt 15 = Real.sqrt (3 * 5) := by norm_num
      rw [h4]
      rw [Real.sqrt_mul]
      all_goals norm_num
    rw [h3, h4]
    <;> ring_nf <;> norm_num
  have h4 : 10 + Real.sqrt 24 + Real.sqrt 40 + Real.sqrt 60 = (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) ^ 2 := by
    rw [h1, h2, h3]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
     Real.sqrt_nonneg 24, Real.sqrt_nonneg 40, Real.sqrt_nonneg 60, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5,
     mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 5), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5)
    ]
  have h5 : Real.sqrt (10 + Real.sqrt 24 + Real.sqrt 40 + Real.sqrt 60) = Real.sqrt ((Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) ^ 2) := by
    rw [h4]
  rw [h5]
  rw [Real.sqrt_sq (by positivity)]
  all_goals positivity