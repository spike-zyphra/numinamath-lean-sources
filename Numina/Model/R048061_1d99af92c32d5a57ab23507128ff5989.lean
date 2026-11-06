import Mathlib

theorem algebra_9029 (a : ℝ) (ha : a < 0) (x : ℝ) :
  x * abs x + abs x - x - a = 0 ↔ x = -1 - Real.sqrt (1 - a) := by
  constructor
  · -- Forward implication
    intro h
    by_cases h1 : x ≥ 0
    · -- x ≥ 0, so |x| = x
      rw [abs_of_nonneg h1] at h
      nlinarith [sq_nonneg (x), sq_nonneg (x + 1), Real.sqrt_nonneg (1 - a), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - a by linarith)]
    · -- x < 0, so |x| = -x
      rw [abs_of_neg (show x < 0 by linarith)] at h
      have h2 : -x ^ 2 - 2 * x - a = 0 := by
        nlinarith 
      have h3 : x ^ 2 + 2 * x + a = 0 := by
        nlinarith [h2]
      have h4 : x < 0 := by
        linarith [show x < (0 : ℝ) by linarith]
      have h5 : (x + 1) ^ 2 = 1 - a := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 - a by linarith), Real.sqrt_nonneg (1 - a)]
      have h6 : x + 1 = -Real.sqrt (1 - a) := by
        nlinarith [Real.sqrt_nonneg (1 - a), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - a by linarith), sq_nonneg (x + 1 + Real.sqrt (1 - a))]
      linarith
  · -- Backward implication
    intro h
    have h1 : x < 0 := by
      nlinarith [Real.sqrt_nonneg (1 - a), Real.sqrt_pos.mpr (by linarith : (1 - a : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - a by linarith)]
    rw [abs_of_neg h1]
    nlinarith [Real.sqrt_nonneg (1 - a), Real.sq_sqrt (show (0 : ℝ) ≤ (1 - a : ℝ) by linarith), sq_nonneg (x + 1)]