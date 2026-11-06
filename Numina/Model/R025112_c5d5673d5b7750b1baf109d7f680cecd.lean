import Mathlib

open Real Set
open scoped Real

theorem inequalities_248368 (x : ℝ) :
  -1/3 ≤ (6 * cos x + sin x - 5)/(2 * cos x - 3 * sin x - 5) ∧
  (6 * cos x + sin x - 5)/(2 * cos x - 3 * sin x - 5) ≤ 3 := by
  constructor
  · -- Prove -1/3 ≤ (6 * cos x + sin x - 5)/(2 * cos x - 3 * sin x - 5)
    have h1 : (2 * cos x - 3 * sin x - 5) ≤ 0 := by
      nlinarith [cos_sq_add_sin_sq x, sq_nonneg (cos x * 3 + sin x * 2), sq_nonneg (cos x - 2 / Real.sqrt 13), sq_nonneg (sin x - 3 / Real.sqrt 13), Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    by_cases h3 : (2 * cos x - 3 * sin x - 5) = 0
    · -- If denominator is 0, then LHS = 0.
      rw [h3]
      norm_num
    · -- If denominator is non-zero
      have h3' : (2 * cos x - 3 * sin x - 5) < 0 := by
        by_contra h
        push_neg at h
        have h4 : (2 * cos x - 3 * sin x - 5) = 0 := by
          linarith
        contradiction
      have h4 : (6 * cos x + sin x - 5) / (2 * cos x - 3 * sin x - 5) ≥ -1 / 3 := by
        apply (le_div_iff_of_neg' h3').mpr
        nlinarith [cos_sq_add_sin_sq x, sq_nonneg (cos x - 11 / 13), sq_nonneg (sin x + 16 / 13), sq_nonneg (2 * cos x - 3 * sin x), sq_nonneg (6 * cos x + sin x - 5), Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
      linarith
  · -- Prove (6 * cos x + sin x - 5)/(2 * cos x - 3 * sin x - 5) ≤ 3
    have h1 : (2 * cos x - 3 * sin x - 5) ≤ 0 := by
      nlinarith [cos_sq_add_sin_sq x, sq_nonneg (cos x * 3 + sin x * 2), sq_nonneg (cos x - 2 / Real.sqrt 13), sq_nonneg (sin x - 3 / Real.sqrt 13), Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    by_cases h3 : (2 * cos x - 3 * sin x - 5) = 0
    · -- If denominator is 0, then LHS = 0.
      rw [h3]
      norm_num
    · -- If denominator is non-zero
      have h3' : (2 * cos x - 3 * sin x - 5) < 0 := by
        by_contra h
        push_neg at h
        have h4 : (2 * cos x - 3 * sin x - 5) = 0 := by
          linarith
        contradiction
      have h5 : (6 * cos x + sin x - 5)/(2 * cos x - 3 * sin x - 5) ≤ 3 := by
        apply (div_le_iff_of_neg' h3').mpr
        nlinarith [cos_sq_add_sin_sq x, sq_nonneg (cos x * 4 - sin x * 6 - 10), sq_nonneg (cos x - 1/5), sq_nonneg (sin x - 12/25), sq_nonneg (2 * cos x - 3 * sin x - 1), sq_nonneg (6 * cos x + sin x - 5), Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
      linarith