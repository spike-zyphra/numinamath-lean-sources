import Mathlib

theorem algebra_293869 {x y : ℝ} (h : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1) :
    x + y = 0 := by
  have h1 : (x + Real.sqrt (x^2 + 1)) ≠ 0 := by
    by_contra h1
    have h2 : (x + Real.sqrt (x ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 0 := by
      rw [h1]
      norm_num
    linarith
  have h2 : (y + Real.sqrt (y^2 + 1)) ≠ 0 := by
    by_contra h2
    have h3 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 0 := by
      rw [h2]
      norm_num
    linarith
  have h3 : (y + Real.sqrt (y^2 + 1)) = (Real.sqrt (x^2 + 1) - x) := by
    have h4 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 1 := h
    have h6 : (x + Real.sqrt (x^2 + 1)) * (Real.sqrt (x^2 + 1) - x) = 1 := by
      nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + 1 by nlinarith), sq_nonneg (x - Real.sqrt (x^2 + 1)), sq_nonneg (x), sq_nonneg (Real.sqrt (x^2 + 1) - x)]
    have h7 : (y + Real.sqrt (y^2 + 1)) = (Real.sqrt (x^2 + 1) - x) := by
      have h11 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = (x + Real.sqrt (x^2 + 1)) * (Real.sqrt (x^2 + 1) - x) := by
        rw [h4, h6]
      have h12 : (x + Real.sqrt (x^2 + 1)) ≠ 0 := h1
      apply (mul_left_inj' h12).mp
      linarith
    exact h7
  have h4 : (x + Real.sqrt (x^2 + 1)) = (Real.sqrt (y^2 + 1) - y) := by
    have h5 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = 1 := h
    have h6 : (y + Real.sqrt (y ^ 2 + 1)) * (Real.sqrt (y^2 + 1) - y) = 1 := by
      nlinarith [Real.sqrt_nonneg (y ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 1 by nlinarith), sq_nonneg (y - Real.sqrt (y^2 + 1)), sq_nonneg (y), sq_nonneg (Real.sqrt (y ^ 2 + 1) - y)]
    have h7 : (x + Real.sqrt (x^2 + 1)) = (Real.sqrt (y^2 + 1) - y) := by
      have h11 : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = (y + Real.sqrt (y ^ 2 + 1)) * (Real.sqrt (y^2 + 1) - y) := by
        rw [h5, h6]
      have h12 : (y + Real.sqrt (y ^ 2 + 1)) ≠ 0 := h2
      apply (mul_left_inj' h12).mp
      linarith
    exact h7
  nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg (y ^ 2 + 1), 
            Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 1 by nlinarith), 
            Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 1 by nlinarith), 
            sq_nonneg (x + y), sq_nonneg (Real.sqrt (x^2 + 1) - Real.sqrt (y^2 + 1)), 
            h3, h4]