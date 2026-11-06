import Mathlib

theorem algebra_103445 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : 2 * Real.sqrt x + Real.sqrt y = Real.sqrt ((x + 1) * (y + 4))) :
    Real.sqrt x * Real.sqrt y = 2 := by
  have h1 : (2 * Real.sqrt x + Real.sqrt y) ^ 2 = (Real.sqrt ((x + 1) * (y + 4))) ^ 2 := by 
    rw [h]
  have h2 : (2 * Real.sqrt x + Real.sqrt y) ^ 2 = 4 * x + y + 4 * (Real.sqrt x * Real.sqrt y) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith), Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg ((x + 1) * (y + 4)), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  have h3 : (Real.sqrt ((x + 1) * (y + 4))) ^ 2 = (x + 1) * (y + 4) := by
    rw [Real.sq_sqrt]
    positivity
  rw [h2, h3] at h1
  nlinarith [sq_nonneg (Real.sqrt x * Real.sqrt y - 2), sq_nonneg (x * y - 4), Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith), mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]