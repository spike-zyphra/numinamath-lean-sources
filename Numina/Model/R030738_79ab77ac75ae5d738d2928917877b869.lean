import Mathlib

open Real Set

theorem algebra_309781 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    sqrt (a^2 + b^2) + sqrt (b^2 + c^2) + sqrt (c^2 + a^2) ≥
    sqrt 2 * (a + b + c) := by
  have h1 : sqrt (a^2 + b^2) ≥ Real.sqrt 2 / 2 * (a + b) := by
    have h2 : (Real.sqrt (a^2 + b^2)) ^ 2 ≥ (Real.sqrt 2 / 2 * (a + b)) ^ 2 := by
      have h3 : (Real.sqrt (a^2 + b^2)) ^ 2 = a^2 + b^2 := by
        rw [Real.sq_sqrt]
        positivity
      have h4 : (Real.sqrt 2 / 2 * (a + b)) ^ 2 = (Real.sqrt 2) ^ 2 / 4 * (a + b) ^ 2 := by ring
      rw [h3, h4]
      nlinarith [sq_nonneg (a - b), Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (a + b)]
    have h4 : sqrt (a ^ 2 + b ^ 2) ≥ 0 := by positivity
    have h5 : Real.sqrt 2 / 2 * (a + b) ≥ 0 := by nlinarith [Real.sqrt_nonneg 2, ha, hb]
    nlinarith [Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), h2]
  have h2 : sqrt (b^2 + c^2) ≥ Real.sqrt 2 / 2 * (b + c) := by
    have h3 : (Real.sqrt (b^2 + c^2)) ^ 2 ≥ (Real.sqrt 2 / 2 * (b + c)) ^ 2 := by
      have h4 : (Real.sqrt (b^2 + c^2)) ^ 2 = b^2 + c^2 := by
        rw [Real.sq_sqrt]
        positivity
      have h5 : (Real.sqrt 2 / 2 * (b + c)) ^ 2 = (Real.sqrt 2) ^ 2 / 4 * (b + c) ^ 2 := by ring
      rw [h4, h5]
      nlinarith [sq_nonneg (b - c), Real.sqrt_nonneg (b ^ 2 + c ^ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (b + c)]
    have h4 : sqrt (b ^ 2 + c ^ 2) ≥ 0 := by positivity
    have h5 : Real.sqrt 2 / 2 * (b + c) ≥ 0 := by nlinarith [Real.sqrt_nonneg 2, hb, hc]
    nlinarith [Real.sqrt_nonneg (b ^ 2 + c ^ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), h3]
  have h3 : sqrt (c^2 + a^2) ≥ Real.sqrt 2 / 2 * (c + a) := by
    have h4 : (Real.sqrt (c^2 + a^2)) ^ 2 ≥ (Real.sqrt 2 / 2 * (c + a)) ^ 2 := by
      have h5 : (Real.sqrt (c^2 + a^2)) ^ 2 = c^2 + a^2 := by
        rw [Real.sq_sqrt]
        positivity
      have h6 : (Real.sqrt 2 / 2 * (c + a)) ^ 2 = (Real.sqrt 2) ^ 2 / 4 * (c + a) ^ 2 := by ring
      rw [h5, h6]
      nlinarith [sq_nonneg (c - a), Real.sqrt_nonneg (c ^ 2 + a ^ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (c + a)]
    have h7 : sqrt (c^2 + a^2) ≥ 0 := by positivity
    have h8 : Real.sqrt 2 / 2 * (c + a) ≥ 0 := by nlinarith [Real.sqrt_nonneg 2, hc, ha]
    nlinarith [Real.sqrt_nonneg (c ^ 2 + a ^ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), h4]
  linarith [h1, h2, h3, Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sqrt_nonneg (b ^ 2 + c ^ 2), Real.sqrt_nonneg (c ^ 2 + a ^ 2), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]