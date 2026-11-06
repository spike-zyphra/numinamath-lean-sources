import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_148557 (x : ℝ) :
  abs (x^3 - 2*x^2 + 2) ≥ 2 - 3*x ↔ x ≤ (1 - sqrt 17)/2 ∨ x ≥ 0 := by
  constructor
  · -- Assume abs (x^3 - 2*x^2 + 2) ≥ 2 - 3*x, prove x ≤ (1 - sqrt 17)/2 ∨ x ≥ 0
    intro h
    by_cases h1 : (x^3 - 2*x^2 + 2) ≥ 0
    · -- When x^3 - 2*x^2 + 2 ≥ 0, abs (x^3 - 2*x^2 + 2) = x^3 - 2*x^2 + 2
      have h2 : abs (x^3 - 2*x^2 + 2) = x^3 - 2*x^2 + 2 := abs_of_nonneg h1
      rw [h2] at h
      have h3 : x^3 - 2*x^2 + 3*x ≥ 0 := by linarith 
      have h4 : x ≥ 0 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x), sq_nonneg (x - 2)]
      right
      linarith
    · -- When x^3 - 2*x^2 + 2 < 0, abs (x^3 - 2*x^2 + 2) = -(x^3 - 2*x^2 + 2)
      have h2 : abs (x^3 - 2*x^2 + 2) = -(x^3 - 2*x^2 + 2) := by
        rw [abs_of_neg]
        linarith
      rw [h2] at h
      have h5 : x^3 - 2*x^2 - 3*x + 4 ≤ 0 := by linarith 
      have h6 : (x - 1) * (x^2 - x - 4) ≤ 0 := by
        nlinarith [sq_nonneg (x^2 - x - 4), sq_nonneg (x - 1), sq_nonneg (x - 2)]
      by_cases h7 : x ≤ (1 - sqrt 17)/2
      · -- x ≤ (1 - sqrt 17)/2
        left
        exact h7
      · -- x > (1 - sqrt 17)/2
        have h9 : x ≥ 0 := by
          nlinarith [sq_nonneg (x - 1), sq_nonneg (x^2 - x - 4), sq_nonneg (x - (1 + Real.sqrt 17)/2), sq_nonneg (x - (1 - Real.sqrt 17)/2), Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num)]
        right
        linarith
  · -- Assume x ≤ (1 - sqrt 17)/2 ∨ x ≥ 0, prove abs (x^3 - 2*x^2 + 2) ≥ 2 - 3*x
    rintro (h | h)
    · -- Case x ≤ (1 - sqrt 17)/2
      have h4 : x^3 - 2*x^2 - 3*x + 4 ≤ 0 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x - (1 + Real.sqrt 17)/2), sq_nonneg (x - (1 - Real.sqrt 17)/2), Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), sq_nonneg (x^2 -x - 4)]
      by_cases h1 : (x^3 - 2*x^2 + 2) ≥ 0
      · -- When x^3 - 2*x^2 + 2 ≥ 0, abs (x^3 - 2*x^2 + 2) = x^3 - 2*x^2 + 2
        rw [abs_of_nonneg h1]
        nlinarith
      · -- When x^3 - 2*x^2 + 2 < 0, abs (x^3 - 2*x^2 + 2) = -(x^3 - 2*x^2 + 2)
        rw [abs_of_neg (by nlinarith)]
        linarith
    · -- Case x ≥ 0
      have h1 : (x^3 - 2*x^2 + 2) ≥ 0 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x), sq_nonneg (x - 2)]
      rw [abs_of_nonneg h1]
      nlinarith