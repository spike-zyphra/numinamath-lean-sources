import Mathlib

theorem algebra_323197 (x : ℝ) (h : 0 ≤ 49 - x^2 ∧ 0 ≤ 25 - x^2) :
    Real.sqrt (49 - x^2) - Real.sqrt (25 - x^2) = 3 ↔
    Real.sqrt (49 - x^2) + Real.sqrt (25 - x^2) = 8 := by
  constructor
  · -- Assume Real.sqrt (49 - x^2) - Real.sqrt (25 - x^2) = 3, we need to prove Real.sqrt (49 - x^2) + Real.sqrt (25 - x^2) = 8
    rintro h1
    have h2 : 0 ≤ 49 - x^2 := h.1
    have h3 : 0 ≤ 25 - x^2 := h.2
    have h4 : Real.sqrt (49 - x^2) ^ 2 = 49 - x^2 := Real.sq_sqrt (show (0 : ℝ) ≤ 49 - x^2 by linarith)
    have h5 : Real.sqrt (25 - x^2) ^ 2 = 25 - x^2 := Real.sq_sqrt (show (0 : ℝ) ≤ 25 - x^2 by linarith)
    have h6 : Real.sqrt (49 - x^2) ^ 2 - Real.sqrt (25 - x^2) ^ 2 = 24 := by
      linarith [h4, h5]
    have h7 : (Real.sqrt (49 - x^2) - Real.sqrt (25 - x^2)) * (Real.sqrt (49 - x^2) + Real.sqrt (25 - x^2)) = 24 := by
      nlinarith
    have h8 : Real.sqrt (49 - x^2) + Real.sqrt (25 - x^2) = 8 := by
      rw [h1] at h7
      nlinarith
    nlinarith [Real.sqrt_nonneg (49 - x^2), Real.sqrt_nonneg (25 - x^2)]
  · -- Assume Real.sqrt (49 - x^2) + Real.sqrt (25 - x^2) = 8, we need to prove Real.sqrt (49 - x^2) - Real.sqrt (25 - x^2) = 3
    rintro h1
    have h2 : 0 ≤ 49 - x^2 := h.1
    have h3 : 0 ≤ 25 - x^2 := h.2
    have h4 : Real.sqrt (49 - x^2) ^ 2 = 49 - x^2 := Real.sq_sqrt (show (0 : ℝ) ≤ 49 - x^2 by linarith)
    have h5 : Real.sqrt (25 - x^2) ^ 2 = 25 - x^2 := Real.sq_sqrt (show (0 : ℝ) ≤ 25 - x^2 by linarith)
    have h6 : Real.sqrt (49 - x^2) ^ 2 - Real.sqrt (25 - x^2) ^ 2 = 24 := by
      linarith [h4, h5]
    have h7 : (Real.sqrt (49 - x^2) + Real.sqrt (25 - x^2)) * (Real.sqrt (49 - x^2) - Real.sqrt (25 - x^2)) = 24 := by
      nlinarith
    have h8 : Real.sqrt (49 - x^2) - Real.sqrt (25 - x^2) = 3 := by
      -- Solve equation to get the result
      rw [show Real.sqrt (49 - x^2) + Real.sqrt (25 - x^2) = 8 by linarith [h1] ] at h7
      nlinarith [Real.sqrt_nonneg (49 - x^2), Real.sqrt_nonneg (25 - x^2)]
    linarith [Real.sqrt_nonneg (49 - x^2), Real.sqrt_nonneg (25 - x^2)]