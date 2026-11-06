import Mathlib

open Real

theorem inequalities_47517 (x y : ℝ) :
    x ^ 2 * sqrt (1 + 2 * y ^ 2) + y ^ 2 * sqrt (1 + 2 * x ^ 2) ≥
    x * y * (x + y + sqrt 2) := by

  have h1 : ∀ t : ℝ, sqrt (1 + 2 * t ^ 2) ≥ t + Real.sqrt 2 / 2 := by
    intro t
    have h2 : (t + Real.sqrt 2 / 2) ^ 2 ≤ 1 + 2 * t ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), sq_nonneg (t - Real.sqrt 2 / 2)]
    have h3 : t + Real.sqrt 2 / 2 ≤ sqrt (1 + 2 * t ^ 2) := by
      by_cases h : t + Real.sqrt 2 / 2 ≥ 0
      · 
        have h4 : (t + Real.sqrt 2 / 2) ^ 2 ≤ 1 + 2 * t ^ 2 := h2
        have h5 : t + Real.sqrt 2 / 2 ≤ Real.sqrt (1 + 2 * t ^ 2) := by
          apply Real.le_sqrt_of_sq_le
          nlinarith
        linarith
      · -- If t + sqrt(2)/2 < 0, then sqrt(1 + 2*t^2) >= 0 > t + sqrt(2)/2
        have h4 : t + Real.sqrt 2 / 2 < 0 := by linarith
        have h6 : Real.sqrt (1 + 2 * t ^ 2) ≥ 0 := Real.sqrt_nonneg (1 + 2 * t ^ 2)
        nlinarith [Real.sqrt_nonneg (1 + 2 * t ^ 2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + 2 * t ^ 2) by nlinarith : (1 + 2 * t ^ 2) ≥ 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
    linarith

  have h3 : x ^ 2 * sqrt (1 + 2 * y ^ 2) ≥ x ^ 2 * (y + Real.sqrt 2 / 2) := by
    have h4 : sqrt (1 + 2 * y ^ 2) ≥ y + Real.sqrt 2 / 2 := by
      apply h1
    have h5 : x ^ 2 ≥ 0 := sq_nonneg x
    nlinarith [Real.sqrt_nonneg (1 + 2 * y ^ 2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]

  have h4 : y ^ 2 * sqrt (1 + 2 * x ^ 2) ≥ y ^ 2 * (x + Real.sqrt 2 / 2) := by
    have h5 : sqrt (1 + 2 * x ^ 2) ≥ x + Real.sqrt 2 / 2 := by
      apply h1
    have h6 : y ^ 2 ≥ 0 := sq_nonneg y
    nlinarith [Real.sqrt_nonneg (1 + 2 * x ^ 2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]

  have h7 : x ^ 2 * sqrt (1 + 2 * y ^ 2) + y ^ 2 * sqrt (1 + 2 * x ^ 2) ≥ x ^ 2 * (y + Real.sqrt 2 / 2) + y ^ 2 * (x + Real.sqrt 2 / 2) := by
    linarith [h3, h4]

  have h8 : x ^ 2 * (y + Real.sqrt 2 / 2) + y ^ 2 * (x + Real.sqrt 2 / 2) ≥ x * y * (x + y + Real.sqrt 2) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0), sq_nonneg (x - y), sq_nonneg (x - Real.sqrt 2 / 2), sq_nonneg (y - Real.sqrt 2 / 2)]

  linarith [h7, h8]