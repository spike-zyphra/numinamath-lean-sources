import Mathlib

theorem algebra_302899 {x y : ℝ} (h : (x + Real.sqrt (x ^ 2 + 2008)) * (y + Real.sqrt (y ^ 2 + 2008)) = 2008) :
    x ^ 2 - 3 * x * y - 4 * y ^ 2 - 6 * x - 6 * y + 2008 = 2008 := by
  have h1 : x + Real.sqrt (x ^ 2 + 2008) ≠ 0 := by
    by_contra h1
    have h2 : (x + Real.sqrt (x ^ 2 + 2008)) * (y + Real.sqrt (y ^ 2 + 2008)) = 0 := by
      rw [h1]
      norm_num
    nlinarith
  -- prove that $y + \sqrt{y^2 + 2008} = \sqrt{x^2 + 2008} - x$
  have h2 : (y + Real.sqrt (y ^ 2 + 2008)) = Real.sqrt (x ^ 2 + 2008) - x := by
    have h3 : (x + Real.sqrt (x ^ 2 + 2008)) * (y + Real.sqrt (y ^ 2 + 2008)) = 2008 := h
    have h4 : (x + Real.sqrt (x ^ 2 + 2008)) * (Real.sqrt (x ^ 2 + 2008) - x) = 2008 := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 2008), Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 2008 by nlinarith)]
    have h5 : (x + Real.sqrt (x ^ 2 + 2008)) * (y + Real.sqrt (y ^ 2 + 2008)) =
        (x + Real.sqrt (x ^ 2 + 2008)) * (Real.sqrt (x ^ 2 + 2008) - x) := by
      nlinarith [h, h4]
    have h6 : (y + Real.sqrt (y ^ 2 + 2008)) = Real.sqrt (x ^ 2 + 2008) - x := by
      apply (mul_left_inj' h1).mp
      linarith
    linarith
  -- prove that $x + \sqrt{x^2 + 2008} = \sqrt{y^2 + 2008} - y$
  have h7 : (x + Real.sqrt (x ^ 2 + 2008)) = Real.sqrt (y ^ 2 + 2008) - y := by
    have h8 : (y + Real.sqrt (y ^ 2 + 2008)) * (x + Real.sqrt (x ^ 2 + 2008)) = 2008 := by
      linarith [h]
    have h9 : (y + Real.sqrt (y ^ 2 + 2008)) * (Real.sqrt (y ^ 2 + 2008) - y) = 2008 := by
      nlinarith [Real.sqrt_nonneg (y ^ 2 + 2008), Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 2008 by nlinarith)]
    have h10 : (y + Real.sqrt (y ^ 2 + 2008)) * (x + Real.sqrt (x ^ 2 + 2008)) =
        (y + Real.sqrt (y ^ 2 + 2008)) * (Real.sqrt (y ^ 2 + 2008) - y) := by
      nlinarith [h8, h9]
    have h11 : (x + Real.sqrt (x ^ 2 + 2008)) = Real.sqrt (y ^ 2 + 2008) - y := by
      apply (mul_left_inj' (show y + Real.sqrt (y ^ 2 + 2008) ≠ 0 by
        by_contra h12
        have h13 : (y + Real.sqrt (y ^ 2 + 2008)) * (x + Real.sqrt (x ^ 2 + 2008)) = 0 := by
          rw [h12]
          norm_num
        nlinarith [h]
      )).mp
      linarith
    linarith
  -- solving the previous two equations we get $y = -x$
  have h8 : y = -x := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 2008), Real.sqrt_nonneg (y ^ 2 + 2008), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 2008 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 2008 by nlinarith)]
  -- substituting into the desired expression
  rw [h8]
  nlinarith