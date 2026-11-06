import Mathlib

theorem algebra_318968 {x y : ℝ} (h : (x + Real.sqrt (x ^ 2 + 2002)) * (y + Real.sqrt (y ^ 2 + 2002)) = 2002) :
    x ^ 2 - 3 * x * y - 4 * y ^ 2 - 6 * x - 6 * y + 58 = 58 := by
  have h1 : y = -x := by
    have h2 : x + Real.sqrt (x ^ 2 + 2002) ≠ 0 := by
      by_contra h2
      have eq1 : (x + Real.sqrt (x ^ 2 + 2002)) * (y + Real.sqrt (y ^ 2 + 2002)) = 2002 := h
      rw [h2] at eq1
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 2002), Real.sqrt_nonneg (y ^ 2 + 2002),
        Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 2002 by nlinarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 2002 by nlinarith),
        sq_nonneg (x - y), sq_nonneg (x + y)]
    have h3 : y + Real.sqrt (y ^ 2 + 2002) ≠ 0 := by
      by_contra h3
      have eq1 : (x + Real.sqrt (x ^ 2 + 2002)) * (y + Real.sqrt (y ^ 2 + 2002)) = 2002 := h
      rw [h3] at eq1
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 2002), Real.sqrt_nonneg (y ^ 2 + 2002),
        Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 2002 by nlinarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 2002 by nlinarith),
        sq_nonneg (x - y), sq_nonneg (x + y)]
    have h4 : (Real.sqrt (x ^ 2 + 2002) - x) = y + Real.sqrt (y ^ 2 + 2002) := by
      have eq1 : (x + Real.sqrt (x ^ 2 + 2002)) * (y + Real.sqrt (y ^ 2 + 2002)) = 2002 := h
      have eq2 : (x + Real.sqrt (x ^ 2 + 2002)) * (Real.sqrt (x ^ 2 + 2002) - x) = 2002 := by
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 2002), Real.sqrt_nonneg (y ^ 2 + 2002),
          Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 2002 by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 2002 by nlinarith),
          sq_nonneg (Real.sqrt (x ^ 2 + 2002) - x), sq_nonneg (Real.sqrt (y ^ 2 + 2002) - y)]
      have eq4 : (Real.sqrt (x ^ 2 + 2002) - x) = y + Real.sqrt (y ^ 2 + 2002) := by
        apply (mul_left_inj' h2).mp
        linarith [eq1, eq2]
      linarith
    have h5 : (Real.sqrt (y ^ 2 + 2002) - y) = x + Real.sqrt (x ^ 2 + 2002) := by
      have eq1 : (x + Real.sqrt (x ^ 2 + 2002)) * (y + Real.sqrt (y ^ 2 + 2002)) = 2002 := h
      have eq3 : (y + Real.sqrt (y ^ 2 + 2002)) * (Real.sqrt (y ^ 2 + 2002) - y) = 2002 := by
        nlinarith [Real.sqrt_nonneg (x ^ 2 + 2002), Real.sqrt_nonneg (y ^ 2 + 2002),
          Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 2002 by nlinarith),
          Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 2002 by nlinarith),
          sq_nonneg (Real.sqrt (x ^ 2 + 2002) - x), sq_nonneg (Real.sqrt (y ^ 2 + 2002) - y)]
      have eq5 : (Real.sqrt (y ^ 2 + 2002) - y) = x + Real.sqrt (x ^ 2 + 2002) := by
        apply (mul_left_inj' h3).mp
        linarith [eq1, eq3]
      linarith
    nlinarith [Real.sqrt_nonneg (x ^ 2 + 2002), Real.sqrt_nonneg (y ^ 2 + 2002),
      Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 2002 by nlinarith),
      Real.sq_sqrt (show (0 : ℝ) ≤ y ^ 2 + 2002 by nlinarith),
      sq_nonneg (Real.sqrt (x ^ 2 + 2002) - x), sq_nonneg (Real.sqrt (y ^ 2 + 2002) - y)]
  rw [h1]
  nlinarith [Real.sqrt_nonneg (x ^ 2 + 2002), Real.sqrt_nonneg ((-x) ^ 2 + 2002),
    Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 + 2002 by nlinarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ (-x) ^ 2 + 2002 by nlinarith),
    sq_nonneg (x + Real.sqrt (x ^ 2 + 2002)), sq_nonneg ((-x) + Real.sqrt ((-x) ^ 2 + 2002))]