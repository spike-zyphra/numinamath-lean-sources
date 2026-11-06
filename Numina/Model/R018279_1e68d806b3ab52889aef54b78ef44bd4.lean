import Mathlib

theorem algebra_313839 (x : ℝ) (hx : x^2 + 32 ≤ 65) (h : Real.sqrt (x^2 + 32) - Real.sqrt (65 - x^2) = 5) :
    3 * Real.sqrt (x^2 + 32) + 2 * Real.sqrt (65 - x^2) = 35 := by

  have h1 : x^2 ≤ 33 := by 
    nlinarith

  have h11 : 0 ≤ Real.sqrt (x^2 + 32) := Real.sqrt_nonneg (x^2 + 32)
  have h12 : 0 ≤ Real.sqrt (65 - x^2) := Real.sqrt_nonneg (65 - x^2)
  have eq6 : Real.sqrt (x^2 + 32) ^ 2 + Real.sqrt (65 - x^2) ^ 2 = 97 := by
    have h7 : Real.sqrt (x^2 + 32) ^ 2 = x^2 + 32 := by 
      have h2 : x^2 + 32 ≥ 0 := by nlinarith
      rw [Real.sq_sqrt h2]
    have h8 : Real.sqrt (65 - x^2) ^ 2 = 65 - x^2 := by 
      have h2 : 65 - x^2 ≥ 0 := by nlinarith
      rw [Real.sq_sqrt h2]
    nlinarith
  
  have h7 : Real.sqrt (65 - x^2) = 4 := by 
    nlinarith [sq_nonneg (Real.sqrt (x^2 + 32) - 9), sq_nonneg (Real.sqrt (65 - x^2) - 4), Real.sqrt_nonneg (x^2 + 32), Real.sqrt_nonneg (65 - x^2)]

  have h8 : Real.sqrt (x^2 + 32) = 9 := by 
    nlinarith [h, h7, Real.sqrt_nonneg (x^2 + 32), Real.sqrt_nonneg (65 - x^2)]

  have h9 : x^2 = 49 := by 
    have h10 : Real.sqrt (x^2 + 32) = 9 := h8
    have h11 : (Real.sqrt (x^2 + 32)) ^ 2 = 81 := by
      rw [h10]
      norm_num
    have h12 : (Real.sqrt (x^2 + 32)) ^ 2 = x^2 + 32 := by
      have h2 : x^2 + 32 ≥ 0 := by nlinarith
      rw [Real.sq_sqrt h2]
    linarith

  nlinarith