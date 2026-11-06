import Mathlib

theorem algebra_296740 (x : ℝ) (hx : x ≥ 0) :
    x^2 - x - 1000 * Real.sqrt (1 + 8000 * x) = 1000 ↔ x = 2001 := by
  constructor
  · -- Assume x^2 - x - 1000 * Real.sqrt (1 + 8000 * x) = 1000 prove x = 2001.
    intro h 
    have h1 : Real.sqrt (1 + 8000 * x) ≥ 0 := by positivity
    have h2 : x ^ 2 - x - 1000 * Real.sqrt (1 + 8000 * x) = 1000 := h
    have h3 : x ^ 2 - x - 1000 ≥ 0 := by 
      nlinarith [Real.sqrt_nonneg (1 + 8000 * x), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8000 * x by nlinarith [hx]), h, sq_nonneg (x ^ 2 - x - 1000 * Real.sqrt (1 + 8000 * x) - 1000), sq_nonneg (Real.sqrt (1 + 8000 * x) - 4001)]
    have h4 : (x ^ 2 - x - 1000) ^ 2 = (1000 * Real.sqrt (1 + 8000 * x)) ^ 2 := by 
      have h5 : x ^ 2 - x - 1000 * Real.sqrt (1 + 8000 * x) = 1000 := h 
      nlinarith 
    have h7 : (1000 * Real.sqrt (1 + 8000 * x)) ^ 2 = 1000000 * (1 + 8000 * x) := by 
      calc 
        (1000 * Real.sqrt (1 + 8000 * x)) ^ 2 
          = 1000000 * (Real.sqrt (1 + 8000 * x) ^ 2) := by ring_nf 
        _ = 1000000 * (1 + 8000 * x) := by 
          rw [Real.sq_sqrt]
          nlinarith 
    have h8 : (x ^ 2 - x - 1000) ^ 2 = 1000000 * (1 + 8000 * x) := by 
      linarith [h4, h7]
    have h5 : (x - 2001) * (x + 2000) = 0 := by
      nlinarith [sq_nonneg (x^2 - x - 1000), sq_nonneg (Real.sqrt (1 + 8000 * x) - 4001), sq_nonneg (x - 2001), sq_nonneg (x + 2000), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ Real.sqrt (1 + 8000 * x) by positivity)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- x - 2001 = 0
      linarith
    · -- x + 2000 = 0
      nlinarith
  · -- Assume x = 2001 prove equation. 
    intro h
    rw [h]
    have h1 : Real.sqrt (1 + 8000 * (2001 : ℝ)) = (4001 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    nlinarith