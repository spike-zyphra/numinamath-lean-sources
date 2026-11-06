import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_148667 (x : ℝ) :
  abs (x^3 + 2 * x^2 - 2) ≥ -2 - 3 * x ↔
  x ≤ (-1 - sqrt 17) / 2 ∨ x ≥ -1 := by
  constructor
  · -- Assume abs (x^3 + 2 * x^2 - 2) ≥ -2 - 3 * x, prove x ≤ (-1 - sqrt 17) / 2 ∨ x ≥ -1
    intro h
    by_cases h1 : x^3 + 2 * x^2 - 2 ≥ 0
    · -- In this case abs (x^3 + 2 * x^2 - 2) = x^3 + 2 * x^2 - 2
      rw [abs_of_nonneg h1] at h
      have h2 : x ≥ -1 := by nlinarith [sq_nonneg (x + 1)]
      right
      linarith
    · -- In this case abs (x^3 + 2 * x^2 - 2) = -(x^3 + 2 * x^2 - 2)
      rw [abs_of_neg (not_le.mp h1)] at h
      have h2 : x^3 + 2 * x^2 - 3 * x - 4 ≤ 0 := by linarith
      by_cases h3 : x ≥ -1
      · -- If x ≥ -1, we can conclude the right disjunction
        right
        linarith
      · -- x < -1, so we need to show x ≤ (-1 - sqrt 17) / 2
        push_neg at h3
        have h4 : x ≤ (-1 - Real.sqrt 17) / 2 := by
          nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), sq_nonneg (x + 1), sq_nonneg (x - (-1 + Real.sqrt 17) / 2), sq_nonneg (x - (-1 - Real.sqrt 17) / 2)]
        left
        linarith
  · -- Assume x ≤ (-1 - sqrt 17) / 2 ∨ x ≥ -1, prove abs (x^3 + 2 * x^2 - 2) ≥ -2 - 3 * x
    rintro (h | h)
    · -- Assume x ≤ (-1 - sqrt 17) / 2
      by_cases h1 : x^3 + 2 * x^2 - 2 ≥ 0
      · -- In this case abs (x^3 + 2 * x^2 - 2) = x^3 + 2 * x^2 - 2
        rw [abs_of_nonneg h1]
        nlinarith [sq_nonneg (x + 1), Real.sqrt_nonneg 17, Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), sq_nonneg (x - (-1 - Real.sqrt 17) / 2)]
      · -- In this case abs (x^3 + 2 * x^2 - 2) = -(x^3 + 2 * x^2 - 2)
        rw [abs_of_neg (not_le.mp h1)]
        nlinarith [sq_nonneg (x + 1), Real.sqrt_nonneg 17, Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), sq_nonneg (x - (-1 - Real.sqrt 17) / 2)]
    · -- Assume x ≥ -1
      by_cases h1 : x^3 + 2 * x^2 - 2 ≥ 0
      · -- In this case abs (x^3 + 2 * x^2 - 2) = x^3 + 2 * x^2 - 2
        rw [abs_of_nonneg h1]
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2 + 2 * x + 3)]
      · -- In this case abs (x^3 + 2 * x^2 - 2) = -(x^3 + 2 * x^2 - 2)
        rw [abs_of_neg (not_le.mp h1)]
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2 + 2 * x + 3)]