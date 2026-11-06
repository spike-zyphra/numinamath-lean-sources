import Mathlib

theorem algebra_186276 : Real.sqrt (4 + Real.sqrt 7) - Real.sqrt (4 - Real.sqrt 7) - Real.sqrt 2 = 0 := by
  have h1 : 0 ≤ Real.sqrt 7 := by positivity
  have h2 : Real.sqrt 7 ≥ 0 := by positivity
  have h3 : 4 + Real.sqrt 7 ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
  have h4 : 4 - Real.sqrt 7 ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), sq_nonneg (4 ^ 2 - (Real.sqrt 7) ^ 2)]
  have h5 : Real.sqrt (4 + Real.sqrt 7) = (Real.sqrt 14 + Real.sqrt 2) / 2 := by
    have h7 : ((Real.sqrt 14 + Real.sqrt 2) / 2) ^ 2 = 4 + Real.sqrt 7 := by
      nlinarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (14 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 14) (Real.sqrt_nonneg 2)]
    have h8 : 0 ≤ (Real.sqrt 14 + Real.sqrt 2) / 2 := by positivity
    rw [Real.sqrt_eq_iff_sq_eq] <;> (nlinarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg 2, h7, h8])
  have h6 : Real.sqrt (4 - Real.sqrt 7) = (Real.sqrt 14 - Real.sqrt 2) / 2 := by
    have h7 : ((Real.sqrt 14 - Real.sqrt 2) / 2) ^ 2 = 4 - Real.sqrt 7 := by
      nlinarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (14 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 14) (Real.sqrt_nonneg 2)]
    have h8 : 0 ≤ (Real.sqrt 14 - Real.sqrt 2) / 2 := by
      have h71 : Real.sqrt 14 ≥ Real.sqrt 2 := by
        apply Real.sqrt_le_sqrt
        norm_num
      linarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg 2, h71]
    rw [Real.sqrt_eq_iff_sq_eq] <;> (nlinarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg 2, h7, h8])
  rw [h5, h6]
  ring_nf
  <;> nlinarith [Real.sqrt_nonneg 14, Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (14 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 14) (Real.sqrt_nonneg 2)]