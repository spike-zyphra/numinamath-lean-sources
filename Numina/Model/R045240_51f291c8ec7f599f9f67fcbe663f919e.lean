import Mathlib

open Real

theorem algebra_97583 {T : ℝ}
    (hT : T = 1 / (3 - √8) - 1 / (√8 - √7) + 1 / (√7 - √6) -
      1 / (√6 - √5) + 1 / (√5 - 2)) :
    T = 5 := by

  have h2 : 1 / (3 - √8) = 3 + √8 := by
    have h8 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    field_simp [(show (3 : ℝ) - √8 ≠ 0 by
      nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num), Real.sqrt_nonneg 8]
    )]
    <;> nlinarith
  have h3 : 1 / (√8 - √7) = √8 + √7 := by
    have h8 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
    have h7 : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    field_simp [(show √8 - √7 ≠ 0 by
      nlinarith [Real.sqrt_nonneg 8, Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_le_sqrt (by norm_num : (7 : ℝ) ≤ (8 : ℝ))]
    )]
    <;> nlinarith
  have h4 : 1 / (√7 - √6) = √7 + √6 := by
    have h7 : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    field_simp [(show √7 - √6 ≠ 0 by
      nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_le_sqrt (by norm_num : (6 : ℝ) ≤ (7 : ℝ))]
    )]
    <;> nlinarith
  have h5 : 1 / (√6 - √5) = √6 + √5 := by
    have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    field_simp [(show √6 - √5 ≠ 0 by
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_le_sqrt (by norm_num : (5 : ℝ) ≤ (6 : ℝ))]
    )]
    <;> nlinarith
  have h6 : 1 / (√5 - 2) = √5 + 2 := by
    have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    field_simp [(show (Real.sqrt 5 : ℝ) - 2 ≠ 0 by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    )]
    <;> nlinarith
  rw [hT]
  rw [h2, h3, h4, h5, h6]
  have h8 : √8 = 2 * √2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, Real.sqrt_nonneg 7, Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num), sq_nonneg (√2 - 1), sq_nonneg (√5 - 2)]