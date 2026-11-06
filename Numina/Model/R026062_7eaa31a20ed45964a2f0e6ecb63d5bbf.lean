import Mathlib

theorem algebra_243601 {x y : ℝ} (h : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1) : x + y = 0 := by

  have h1 : x + Real.sqrt (x ^ 2 + 1) ≠ 0 := by
    by_contra h1
    rw [h1] at h
    nlinarith

  have h2 : y + Real.sqrt (y ^ 2 + 1) ≠ 0 := by
    by_contra h2
    rw [h2] at h
    nlinarith
  
  have h3 : (x + Real.sqrt (x ^ 2 + 1)) * (Real.sqrt (x ^ 2 + 1) - x) = 1 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by nlinarith)]

  have h4 : (y + Real.sqrt (y ^ 2 + 1)) * (Real.sqrt (y ^ 2 + 1) - y) = 1 := by
    nlinarith [Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 1 by nlinarith)]
  
  -- deriving that real square roots expressions equal inverses.
  have h5 : Real.sqrt (x ^ 2 + 1) - x = (y + Real.sqrt (y ^ 2 + 1)) := by
    have h6 : (x + Real.sqrt (x ^ 2 + 1)) * (Real.sqrt (x ^ 2 + 1) - x) = 1 := h3
    have h7 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1 := h
    have : (Real.sqrt (x ^ 2 + 1) - x) = (y + Real.sqrt (y ^ 2 + 1)) := by
      apply (mul_left_inj' h1).mp
      linarith
    linarith

  -- deriving that real square roots expressions equal inverses.
  have h6 : Real.sqrt (y ^ 2 + 1) - y = (x + Real.sqrt (x ^ 2 + 1)) := by
    have h7 : (y + Real.sqrt (y ^ 2 + 1)) * (Real.sqrt (y ^ 2 + 1) - y) = 1 := h4
    have h8 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1 := h
    have : (Real.sqrt (y ^ 2 + 1) - y) = (x + Real.sqrt (x ^ 2 + 1)) := by
      apply (mul_left_inj' h2).mp
      linarith
    linarith
  
  nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), 
    Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by nlinarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 1 by nlinarith), 
    sq_nonneg (x - y), sq_nonneg (x + y)]