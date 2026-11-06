import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_308619 (x y : ℝ) (h : x^2 + y^2 = 25) :
    sqrt (8 * y - 6 * x + 50) + sqrt (8 * y + 6 * x + 50) ≤ 6 * sqrt 10 := by
  have h1 : 0 ≤ 8 * y - 6 * x + 50 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 4), sq_nonneg (x + 3), sq_nonneg (y + 4)]
  have h2 : 0 ≤ 8 * y + 6 * x + 50 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 4), sq_nonneg (x + 3), sq_nonneg (y + 4)]
  have h3 : (sqrt (8 * y - 6 * x + 50) + sqrt (8 * y + 6 * x + 50)) ^ 2 ≤ 360 := by
    have h4 : (sqrt (8 * y - 6 * x + 50) + sqrt (8 * y + 6 * x + 50)) ^ 2 =
        (sqrt (8 * y - 6 * x + 50)) ^ 2 + (sqrt (8 * y + 6 * x + 50)) ^ 2 + 2 * (sqrt (8 * y - 6 * x + 50) * sqrt (8 * y + 6 * x + 50)) := by
      ring
    rw [h4]
    have h5 : (sqrt (8 * y - 6 * x + 50)) ^ 2 = 8 * y - 6 * x + 50 := by
      apply Real.sq_sqrt
      linarith
    have h6 : (sqrt (8 * y + 6 * x + 50)) ^ 2 = 8 * y + 6 * x + 50 := by
      apply Real.sq_sqrt
      linarith
    rw [h5, h6]
    have h7 : (sqrt (8 * y - 6 * x + 50) * sqrt (8 * y + 6 * x + 50)) =
        Real.sqrt ((8 * y - 6 * x + 50) * (8 * y + 6 * x + 50)) := by
      rw [←Real.sqrt_mul (by
        nlinarith
      )]
      all_goals linarith
    rw [h7]
    have h8 : (8 * y - 6 * x + 50) * (8 * y + 6 * x + 50) = 100 * (y + 4) ^ 2 := by
      nlinarith [h, sq_nonneg (x), sq_nonneg (y * 3)]
    rw [h8]
    have h9 : Real.sqrt (100 * (y + 4) ^ 2) = 10 * |y + 4| := by
      have h10 : Real.sqrt (100 * (y + 4) ^ 2) = Real.sqrt (100 * ((y + 4) ^ 2)) := by
        ring_nf
      rw [h10]
      have h11 : Real.sqrt (100 * ((y + 4) ^ 2)) = Real.sqrt (100) * Real.sqrt (((y + 4) ^ 2)) := by
        rw [Real.sqrt_mul (by
          nlinarith
        )]
      rw [h11]
      have h12 : Real.sqrt (100 : ℝ) = (10 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h13 : Real.sqrt ((y + 4) ^ 2) = |y + 4| := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h12, h13]
      all_goals linarith
    rw [h9]
    by_cases h10 : y + 4 ≥ 0
    · -- y + 4 ≥ 0
      rw [abs_of_nonneg h10]
      nlinarith [sq_nonneg (y - 5), sq_nonneg (x ^ 2 - 9), sq_nonneg (y + 4)]
    · -- y + 4 < 0
      rw [abs_of_neg (not_le.mp h10)]
      nlinarith [sq_nonneg (y + 4), sq_nonneg (x ^ 2 - 9)]
  have h4 : (sqrt (8 * y - 6 * x + 50) + sqrt (8 * y + 6 * x + 50)) ≤ Real.sqrt 360 := by
    apply Real.le_sqrt_of_sq_le
    linarith
    all_goals linarith
  have h5 : Real.sqrt 360 = 6 * Real.sqrt 10 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  linarith [h4, h5, Real.sqrt_nonneg 360, Real.sqrt_nonneg 10, Real.sqrt_nonneg (8 * y - 6 * x + 50), Real.sqrt_nonneg (8 * y + 6 * x + 50)]
  all_goals linarith