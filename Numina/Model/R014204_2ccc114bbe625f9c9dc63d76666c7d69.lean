import Mathlib

theorem inequalities_221542 (x y : ℝ) (h : x ^ 4 + y ^ 4 ≥ 2) :
    abs (x ^ 12 - y ^ 12) + 2 * x ^ 6 * y ^ 6 ≥ 2 := by 
  have h1 : x ^ 6 ≥ 0 := by positivity
  have h2 : y ^ 6 ≥ 0 := by positivity
  have h3 : x ^ 12 ≥ 0 := by positivity
  have h4 : y ^ 12 ≥ 0 := by positivity
  have h5 : x^12 + y^12 ≥ 2 * x^6 * y^6 := by
    nlinarith [sq_nonneg (x^6 - y^6)]
  by_cases h6 : x ^ 6 ≥ y ^ 6
  · -- Assume x^6 ≥ y^6
    have h7 : x ^ 12 - y ^ 12 ≥ 0 := by
      have h8 : x ^ 12 ≥ y ^ 12 := by
        have h9 : x ^ 6 ≥ y ^ 6 := h6
        have h10 : x ^ 12 = (x ^ 6) ^ 2 := by ring
        have h11 : y ^ 12 = (y ^ 6) ^ 2 := by ring
        rw [h10, h11]
        nlinarith [sq_nonneg (x ^ 6 - y ^ 6)]
      linarith 
    rw [abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (x ^ 6 - y ^ 6), sq_nonneg (x ^ 4 - y ^ 4), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg (x^6 * y^6 - 1), mul_nonneg (show (0 : ℝ) ≤ x ^ 6 by positivity) (show (0 : ℝ) ≤ y ^ 6 by positivity), sq_nonneg (x^4 + y^4 - 2), sq_nonneg ((x^6) ^ 2 - (y^6) ^ 2)]
  · -- Assume x^6 < y^6
    have h7 : x ^ 12 - y ^ 12 ≤ 0 := by
      have h8 : x ^ 12 ≤ y ^ 12 := by
        have h6' : x ^ 6 < y ^ 6 := by linarith
        have h10 : x ^ 12 = (x ^ 6) ^ 2 := by ring
        have h11 : y ^ 12 = (y ^ 6) ^ 2 := by ring
        rw [h10, h11]
        nlinarith [sq_nonneg (x ^ 6 - y ^ 6), h6']
      linarith
    rw [abs_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (x ^ 6 - y ^ 6), sq_nonneg (x ^ 4 - y ^ 4), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg (x^6 * y^6 - 1), mul_nonneg (show (0 : ℝ) ≤ x ^ 6 by positivity) (show (0 : ℝ) ≤ y ^ 6 by positivity), sq_nonneg (x^4 + y^4 - 2), sq_nonneg ((x^6) ^ 2 - (y^6) ^ 2)]