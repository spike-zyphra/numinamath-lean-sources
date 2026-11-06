import Mathlib

theorem algebra_179187 (x : ℝ) (hx : 1 ≤ x) :
    x^4 + 2 * x * Real.sqrt (x - 1) + 3 * x^2 - 8 * x + 4 = 0 ↔ x = 1 := by
  constructor
  · -- Assume equation holds, prove x = 1
    intro h_eq
    have h1 : Real.sqrt (x - 1) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h2 : x - 1 ≥ 0 := by linarith
    have h3 : Real.sqrt (x - 1) ^ 2 = x - 1 := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2 - (x + 1) * Real.sqrt (x - 1)), sq_nonneg (x - 1), sq_nonneg (x * Real.sqrt (x - 1) - 1), sq_nonneg (Real.sqrt (x - 1) - 0), sq_nonneg (x ^ 2 - 4 * x + 1), sq_nonneg (Real.sqrt (x - 1) * (x - 1)), sq_nonneg (x ^ 2 - 2 * x), sq_nonneg (x - 2), Real.sqrt_nonneg (x - 1)]
  · -- Assume x = 1 prove equation
    intro h_eq
    rw [h_eq]
    have h_eq : Real.sqrt (1 - 1) = 0 := by
      norm_num [Real.sqrt_zero]
    rw [h_eq]
    norm_num