import Mathlib

theorem algebra_171718 (x : ℝ) (hx : x^2 + 1 ≥ 0) (h : 2 * x + 2 + x * Real.sqrt (x^2 + 1) + (x + 2) * Real.sqrt (x^2 + 4 * x + 5) = 0) :
    x = -1 := by
  have h1 : Real.sqrt (x ^ 2 + 4 * x + 5) = Real.sqrt ((x + 2) ^ 2 + 1) := by
    ring_nf
  rw [h1] at h
  have h2 : Real.sqrt (x ^ 2 + 1) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 1)
  have h3 : Real.sqrt ((x + 2) ^ 2 + 1) ≥ 0 := Real.sqrt_nonneg ((x + 2) ^ 2 + 1)
  have h4 : (Real.sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 := Real.sq_sqrt (by nlinarith)
  have h5 : (Real.sqrt ((x + 2) ^ 2 + 1)) ^ 2 = (x + 2) ^ 2 + 1 := Real.sq_sqrt (by nlinarith)
  nlinarith [sq_nonneg (x + 1), sq_nonneg (Real.sqrt (x ^ 2 + 1) - Real.sqrt ((x + 2) ^ 2 + 1)), sq_nonneg (x * Real.sqrt (x ^ 2 + 1)), sq_nonneg ((x + 2) * Real.sqrt ((x + 2) ^ 2 + 1)), sq_nonneg (Real.sqrt (x ^ 2 + 1) ^ 2 - Real.sqrt ((x + 2) ^ 2 + 1) ^ 2), mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 1)) (Real.sqrt_nonneg ((x + 2) ^ 2 + 1)), h4, h5]