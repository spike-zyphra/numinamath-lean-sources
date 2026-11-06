import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_192458 (x : ℝ) :
  sqrt (x + 3) < sqrt (x - 1) + sqrt (x - 2) ↔
  x > (2 * sqrt 21) / 3 := by
  constructor
  · -- Assume $\sqrt(x + 3) < \sqrt(x - 1) + \sqrt(x - 2)$ prove $x > (2 * \sqrt 21) / 3$
    intro h
    by_cases h1 : x ≥ 2
    · -- Assume x ≥ 2.
      have h2 : sqrt (x + 3) ≥ 0 := by positivity
      have h3 : sqrt (x - 1) ≥ 0 := by positivity
      have h4 : sqrt (x - 2) ≥ 0 := by positivity
      have h5 : (sqrt (x + 3)) ^ 2 < (sqrt (x - 1) + sqrt (x - 2)) ^ 2 := by
        nlinarith [h, Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2)]
      have h6 : (sqrt (x + 3)) ^ 2 = x + 3 := by
        rw [Real.sq_sqrt]
        linarith
      have h7 : (sqrt (x - 1) + sqrt (x - 2)) ^ 2 = (sqrt (x - 1)) ^ 2 + (sqrt (x - 2)) ^ 2 + 2 * (sqrt (x - 1) * sqrt (x - 2)) := by
        ring
      have h8 : (sqrt (x - 1)) ^ 2 = x - 1 := by
        rw [Real.sq_sqrt]
        linarith
      have h9 : (sqrt (x - 2)) ^ 2 = x - 2 := by
        rw [Real.sq_sqrt]
        linarith
      have h10 : (sqrt (x - 1) + sqrt (x - 2)) ^ 2 = (x - 1) + (x - 2) + 2 * (sqrt (x - 1) * sqrt (x - 2)) := by
        rw [h7, h8, h9]
        all_goals nlinarith
      rw [h6, h10] at h5
      have h11 : 6 - x < 2 * (sqrt (x - 1) * sqrt (x - 2)) := by
        nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ (x + 3) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 2) by linarith)]
      have h12 : sqrt (x - 1) * sqrt (x - 2) = Real.sqrt ((x - 1) * (x - 2)) := by
        rw [← Real.sqrt_mul (by nlinarith)]
        all_goals positivity
      rw [h12] at h11
      have h13 : (6 - x) ^ 2 < 4 * ((x - 1) * (x - 2)) := by
        nlinarith [h11, Real.sqrt_nonneg ((x - 1) * (x - 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1) * (x - 2) by nlinarith)]
      have h14 : x ^ 2 > 28 / 3 := by
        nlinarith
      have h16 : x > (2 * Real.sqrt 21) / 3 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (21 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num), Real.sqrt_nonneg 21]
      linarith
      all_goals nlinarith
      all_goals nlinarith
    · -- Assume x < 2
      have h2 : x < 2 := by linarith
      have h3 : sqrt (x - 2) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals try { nlinarith }
      by_cases h5 : x ≥ 1
      · -- Assume 1 ≤ x < 2
        have h6 : sqrt (x - 1) ≥ 0 := by positivity
        have h7 : sqrt (x - 2) = 0 := h3
        have h8 : sqrt (x + 3) < sqrt (x - 1) + sqrt (x - 2) := h
        have h11 : sqrt (x + 3) < sqrt (x - 1) := by
          nlinarith [h8, h7, Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x + 3)]
        have h12 : sqrt (x + 3) ≥ 0 := by positivity
        have h13 : sqrt (x - 1) ≥ 0 := by positivity
        have h14 : (sqrt (x + 3)) ^ 2 < (sqrt (x - 1)) ^ 2 := by
          nlinarith [h11, Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1)]
        have h15 : (sqrt (x + 3)) ^ 2 = x + 3 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h16 : (sqrt (x - 1)) ^ 2 = x - 1 := by
          rw [Real.sq_sqrt]
          nlinarith
        nlinarith
      · -- Assume x < 1
        have h8 : x < 1 := by linarith
        have h9 : sqrt (x - 1) = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
          all_goals try { nlinarith }
        have h3' : sqrt (x - 2) = 0 := h3
        nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2), h3', h9]
  · -- Assume x > (2 * sqrt 21) / 3 prove sqrt (x + 3) < sqrt (x - 1) + sqrt (x - 2)
    intro h
    have h1 : x ≥ 2 := by
      nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num), Real.sqrt_nonneg 21]
    have h2 : sqrt (x + 3) ≥ 0 := by positivity
    have h3 : sqrt (x - 1) ≥ 0 := by positivity
    have h4 : sqrt (x - 2) ≥ 0 := by positivity
    have h16 : x > (2 * Real.sqrt 21) / 3 := h
    have h14 : x ^ 2 > 28 / 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (21 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num), h16, Real.sqrt_nonneg 21]
    have h13 : (6 - x) ^ 2 < 4 * ((x - 1) * (x - 2)) := by
      nlinarith
    have h6 : (sqrt (x + 3)) ^ 2 = x + 3 := by
      rw [Real.sq_sqrt]
      linarith
    have h7 : (sqrt (x - 1) + sqrt (x - 2)) ^ 2 = (sqrt (x - 1)) ^ 2 + (sqrt (x - 2)) ^ 2 + 2 * (sqrt (x - 1) * sqrt (x - 2)) := by
      ring
    have h8 : (sqrt (x - 1)) ^ 2 = x - 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h9 : (sqrt (x - 2)) ^ 2 = x - 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h10 : (sqrt (x - 1) + sqrt (x - 2)) ^ 2 = (x - 1) + (x - 2) + 2 * (sqrt (x - 1) * sqrt (x - 2)) := by
      rw [h7, h8, h9]
      all_goals nlinarith
    have h5 : (sqrt (x + 3)) ^ 2 < (sqrt (x - 1) + sqrt (x - 2)) ^ 2 := by
      rw [h6, h10]
      have h11 : 6 - x < 2 * (sqrt (x - 1) * sqrt (x - 2)) := by
        have h13' : (6 - x) ^ 2 < 4 * ((x - 1) * (x - 2)) := h13
        have h12 : sqrt (x - 1) * sqrt (x - 2) = Real.sqrt ((x - 1) * (x - 2)) := by
          rw [← Real.sqrt_mul (by nlinarith)]
          all_goals positivity
        rw [h12] at *
        have h19 : 0 ≤ (x - 1) * (x - 2) := by nlinarith
        nlinarith [Real.sqrt_nonneg ((x - 1) * (x - 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1) * (x - 2) by nlinarith)]
      nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show (0 : ℝ) ≤ (x + 3) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 2) by linarith)]
    have h17 : sqrt (x + 3) < sqrt (x - 1) + sqrt (x - 2) := by
      nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 2), h5]
    linarith
    all_goals nlinarith
    all_goals nlinarith