import Mathlib

open Real

theorem algebra_16563 {r s : ℝ} (hr : r^2 - r * sqrt 5 + 1 = 0) (hs : s^2 - s * sqrt 5 + 1 = 0)
    (hne : r ≠ s) : r^8 + s^8 = 47 := by

  have h1 : r^2 = r * sqrt 5 - 1 := by linarith
  have h2 : s^2 = s * sqrt 5 - 1 := by linarith

  have h3 : r + s = Real.sqrt 5 := by
    have h4 : (r - s) * (r + s - Real.sqrt 5) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · 
      exfalso
      apply hne
      linarith
    · 
      linarith

  have h4 : r * s = 1 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h3]

  have h5 : r^2 + s^2 = 3 := by
    have h6 : r^2 + s^2 = (r + s) ^ 2 - 2 * (r * s) := by
      nlinarith
    rw [h6, h3, h4]
    have h7 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 5, h7]

  have h6 : r^3 + s^3 = 2 * Real.sqrt 5 := by
    have h7 : r^3 + s^3 = (r + s) * ((r^2 + s^2) - (r * s)) := by
      ring
    rw [h7, h3, h5, h4]
    all_goals
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h7 : r^4 + s^4 = 7 := by
    have h8 : r^4 + s^4 = Real.sqrt 5 * (r^3 + s^3) - (r^2 + s^2) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [h8, h6, h5]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h8 : r^5 + s^5 = 5 * Real.sqrt 5 := by
    have h9 : r^5 + s^5 = Real.sqrt 5 * (r^4 + s^4) - (r^3 + s^3) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [h9, h7, h6]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h9 : r^6 + s^6 = 18 := by
    have h10 : r^6 + s^6 = Real.sqrt 5 * (r^5 + s^5) - (r^4 + s^4) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [h10, h8, h7]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h10 : r^7 + s^7 = 13 * Real.sqrt 5 := by
    have h11 : r^7 + s^7 = Real.sqrt 5 * (r^6 + s^6) - (r^5 + s^5) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [h11, h9, h8]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  have h11 : r^8 + s^8 = 47 := by
    have h12 : r^8 + s^8 = Real.sqrt 5 * (r^7 + s^7) - (r^6 + s^6) := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    rw [h12, h10, h9]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  exact h11