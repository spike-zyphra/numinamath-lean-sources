import Mathlib

theorem algebra_215898 (x : ℝ) : x^6 - 20 * x^2 - Real.sqrt 21 = 0 ↔ x^4 = 21 := by
  constructor
  · -- Assume x^6 - 20 * x^2 - sqrt 21 = 0, prove x^4 = 21
    intro h
    have h1 : x ^ 6 = 20 * x ^ 2 + Real.sqrt 21 := by linarith
    have h2 : x ^ 2 ≥ 0 := by nlinarith
    have h3 : (x ^ 2) ^ 3 = 20 * (x ^ 2) + Real.sqrt 21 := by 
      nlinarith [sq_nonneg (x ^ 2), Real.sqrt_nonneg 21, h1]
    have h4 : x ^ 2 = Real.sqrt 21 := by
      nlinarith [sq_nonneg ((x ^ 2) ^ 2 - 21), sq_nonneg (x ^ 2 - Real.sqrt 21), Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 - 4)]
    have h5 : x ^ 4 = 21 := by
      calc
        x ^ 4 = (x ^ 2) ^ 2 := by ring
        _ = (Real.sqrt 21) ^ 2 := by rw [h4]
        _ = 21 := by rw [Real.sq_sqrt]; linarith
    linarith
  · -- Assume x^4 = 21, prove x^6 - 20 * x^2 - sqrt 21 = 0
    intro h
    have h1 : x ^ 2 ≥ 0 := by nlinarith
    have h2 : x ^ 4 = 21 := h
    have h3 : x ^ 2 = Real.sqrt 21 := by
      have h4 : (x ^ 2) ^ 2 = 21 := by nlinarith [sq_nonneg (x ^ 2)]
      have h5 : x ^ 2 ≥ 0 := by nlinarith
      have h6 : Real.sqrt 21 ≥ 0 := by apply Real.sqrt_nonneg
      have h7 : (x ^ 2) = Real.sqrt 21 := by
        nlinarith [sq_nonneg (x ^ 2 - Real.sqrt 21), Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
      linarith
    have h4 : x ^ 6 = (x ^ 2) ^ 3 := by ring
    rw [h4, h3]
    nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num), sq_nonneg (Real.sqrt 21 ^ 2 - 21)]