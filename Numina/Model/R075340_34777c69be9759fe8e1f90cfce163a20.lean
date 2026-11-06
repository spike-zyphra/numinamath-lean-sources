import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_161041 {x : ℝ} (hx : x ≥ 1) :
    sqrt (x + 2 * sqrt (x - 1)) + sqrt (x - 2 * sqrt (x - 1)) =
    if x ≤ 2 then 2 else 2 * sqrt (x - 1) := by
  by_cases h : x ≤ 2
  · -- Case x ≤ 2
    rw [if_pos h]
    have h1 : sqrt (x + 2 * sqrt (x - 1)) = sqrt (x - 1) + 1 := by
      have h_eq : x + 2 * sqrt (x - 1) = (sqrt (x - 1) + 1) ^ 2 := by
        have h_sqrts : sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
        nlinarith [Real.sqrt_nonneg (x - 1)]
      rw [h_eq]
      have h_abs : sqrt ((sqrt (x - 1) + 1) ^ 2) = sqrt (x - 1) + 1 := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (show sqrt (x - 1) + 1 ≥ 0 by positivity)]
      exact h_abs
    have h2 : sqrt (x - 2 * sqrt (x - 1)) = 1 - sqrt (x - 1) := by
      have h_eq : x - 2 * sqrt (x - 1) = (sqrt (x - 1) - 1) ^ 2 := by
        have h_sqrts : sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
        nlinarith [Real.sqrt_nonneg (x - 1)]
      rw [h_eq]
      have h_abs : sqrt ((sqrt (x - 1) - 1) ^ 2) = 1 - sqrt (x - 1) := by
        rw [Real.sqrt_sq_eq_abs]
        have h_le : sqrt (x - 1) ≤ 1 := by
          have : x - 1 ≤ (1 : ℝ) := by linarith
          have h_sqr : sqrt (x - 1) ≤ sqrt (1 : ℝ) := by
            apply Real.sqrt_le_sqrt (by linarith)
          rw [show sqrt (1 : ℝ) = 1 by simp] at h_sqr
          linarith
        have h_neg : sqrt (x - 1) - 1 ≤ 0 := by
          nlinarith [Real.sqrt_nonneg (x - 1)]
        have : |sqrt (x - 1) - 1| = 1 - sqrt (x - 1) := by
          rw [abs_of_nonpos h_neg]
          all_goals linarith [Real.sqrt_nonneg (x - 1)]
        exact this
      exact h_abs
    rw [h1, h2]
    all_goals nlinarith [Real.sq_sqrt (show x - 1 ≥ 0 by linarith), Real.sqrt_nonneg (x - 1)]
  · -- Case x > 2
    rw [if_neg h]
    have h3 : x > 2 := by linarith
    have h1 : sqrt (x + 2 * sqrt (x - 1)) = sqrt (x - 1) + 1 := by
      have h_eq : x + 2 * sqrt (x - 1) = (sqrt (x - 1) + 1) ^ 2 := by
        have h_sqr : sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
        nlinarith [Real.sqrt_nonneg (x - 1)]
      rw [h_eq]
      have h_abs : sqrt ((sqrt (x - 1) + 1) ^ 2) = sqrt (x - 1) + 1 := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (show sqrt (x - 1) + 1 ≥ 0 by positivity)]
      exact h_abs
    have h2 : sqrt (x - 2 * sqrt (x - 1)) = sqrt (x - 1) - 1 := by
      have h_eq : x - 2 * sqrt (x - 1) = (sqrt (x - 1) - 1) ^ 2 := by
        have h_sqr : sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
        nlinarith [Real.sqrt_nonneg (x - 1)]
      rw [h_eq]
      have h_abs : sqrt ((sqrt (x - 1) - 1) ^ 2) = sqrt (x - 1) - 1 := by
        rw [Real.sqrt_sq_eq_abs]
        have h_gt : sqrt (x - 1) > 1 := by
          have h2 : x - 1 > (1 : ℝ) := by nlinarith
          have h_sqr : sqrt (x - 1) > sqrt (1 : ℝ) := by
            apply Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
          rw [show sqrt (1 : ℝ) = 1 by simp] at h_sqr
          linarith
        have : sqrt (x - 1) - 1 ≥ 0 := by linarith [Real.sqrt_nonneg (x - 1)]
        rw [abs_of_nonneg this]
        all_goals linarith [Real.sqrt_nonneg (x - 1)]
      exact h_abs
    rw [h1, h2]
    all_goals nlinarith [Real.sq_sqrt (show x - 1 ≥ 0 by linarith), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x - 1)]