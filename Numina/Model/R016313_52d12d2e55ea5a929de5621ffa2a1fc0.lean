import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_313779 (x : ℝ) :
  abs (cos x) + abs (cos (2 * x)) ≥ 1 / sqrt 2 := by
  have h1 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
    rw [cos_two_mul]
  rw [h1]
  have h2 : (1 / Real.sqrt 2 : ℝ) = Real.sqrt 2 / 2 := by
    field_simp
    <;> ring_nf <;> norm_num
  rw [h2]
  by_cases h3 : cos x ≥ 0
  · -- Case 1: cos x ≥ 0.
    by_cases h4 : (2 * cos x ^ 2 - 1 : ℝ) ≥ 0
    · -- Case 1a: cos x ≥ 0 and 2 * cos x^2 - 1 ≥ 0.
      rw [abs_of_nonneg h3, abs_of_nonneg h4]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (cos x - Real.sqrt 2 / 2), sq_nonneg (cos x + Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (cos x * 2 - Real.sqrt 2)]
    · -- Case 1b: cos x ≥ 0 and 2 * cos x^2 - 1 < 0.
      rw [abs_of_nonneg h3, abs_of_neg (by nlinarith)]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (cos x - Real.sqrt 2 / 2), sq_nonneg (cos x + Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (cos x * 2 - Real.sqrt 2)]
  · -- Case 2: cos x < 0.
    by_cases h4 : (2 * cos x ^ 2 - 1 : ℝ) ≥ 0
    · -- Case 2a: cos x < 0 and 2 * cos x^2 - 1 ≥ 0.
      rw [abs_of_neg (by nlinarith), abs_of_nonneg h4]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (cos x - Real.sqrt 2 / 2), sq_nonneg (cos x + Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (cos x * 2 - Real.sqrt 2)]
    · -- Case 2b: cos x < 0 and 2 * cos x^2 - 1 < 0.
      rw [abs_of_neg (by nlinarith), abs_of_neg (by nlinarith)]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (cos x - Real.sqrt 2 / 2), sq_nonneg (cos x + Real.sqrt 2 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (cos x * 2 - Real.sqrt 2)]