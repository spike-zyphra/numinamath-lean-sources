import Mathlib

theorem algebra_252259 (x : ℝ) (hx : x = (Real.sqrt (1 + x) + 1) * (Real.sqrt (10 + x) - 4)) :
    x = -1 := by
  by_cases h : x < -1
  · -- Sometimes, square roots can be 0.
    have h1 : x < -1 := h
    have h2 : (1 + x) < (0 : ℝ) := by linarith
    have h3 : Real.sqrt (1 + x) = 0 := by
      rw [Real.sqrt_eq_zero']
      linarith
      all_goals nlinarith
    rw [h3] at hx
    have h5 : Real.sqrt (10 + x) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h6 : Real.sqrt (10 + x) < (3 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (10 + x), Real.sq_sqrt (show (10 + x) ≥ 0 by linarith), sq_nonneg (Real.sqrt (10 + x) - 3), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (10 + x) by linarith)]
    nlinarith [Real.sqrt_nonneg (10 + x), Real.sq_sqrt (show (10 + x) ≥ 0 by linarith), sq_nonneg (Real.sqrt (10 + x) - 3)]
  · -- Then the equation is satisfied
    have h1 : x ≥ -1 := by linarith
    have h2 : (1 + x) ≥ (0 : ℝ) := by linarith
    have h5 : Real.sqrt (1 + x) ≥ 0 := Real.sqrt_nonneg (1 + x)
    have h6 : Real.sqrt (10 + x) ≥ 0 := Real.sqrt_nonneg (10 + x)
    have h7 : (Real.sqrt (1 + x)) ^ 2 = (1 + x) := Real.sq_sqrt (by linarith)
    have h8 : (Real.sqrt (10 + x)) ^ 2 = (10 + x) := Real.sq_sqrt (by linarith)
    nlinarith [sq_nonneg (Real.sqrt (1 + x) - 0), sq_nonneg (Real.sqrt (10 + x) - 3), h7, h8, Real.sqrt_nonneg (10 + x), Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (10 + x), Real.sqrt_nonneg (1 + x), mul_nonneg (Real.sqrt_nonneg (1 + x)) (Real.sqrt_nonneg (10 + x))]