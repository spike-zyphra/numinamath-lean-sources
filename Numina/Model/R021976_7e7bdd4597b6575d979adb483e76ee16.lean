import Mathlib

theorem inequalities_10809 (x y : ℝ) (hx : x ^ 2 ≤ 1) (hy : y ^ 2 ≤ 1)
    (h : x * Real.sqrt (1 - y ^ 2) + y * Real.sqrt (1 - x ^ 2) ≥ 1) :
    x ^ 2 + y ^ 2 = 1 := by

  have h1 : Real.sqrt (1 - y ^ 2) ≥ 0 := by positivity
  have h2 : Real.sqrt (1 - x ^ 2) ≥ 0 := by positivity

  have h3 : (1 - y ^ 2 : ℝ) ≥ 0 := by nlinarith
  have h4 : (1 - x ^ 2 : ℝ) ≥ 0 := by nlinarith

  have h6 : (Real.sqrt (1 - y ^ 2)) ^ 2 = 1 - y ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith

  have h7 : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := by
    rw [Real.sq_sqrt]
    nlinarith

  nlinarith [sq_nonneg (x ^ 2 + y ^ 2 - 1), sq_nonneg (x - y), sq_nonneg (Real.sqrt (1 - y ^ 2) - Real.sqrt (1 - x ^ 2)), sq_nonneg (x * Real.sqrt (1 - y^2) - y * Real.sqrt (1 -x^2)), sq_nonneg (x * Real.sqrt (1 -x^2) - y * Real.sqrt (1 -y^2)), Real.sqrt_nonneg (1 - y ^ 2), Real.sqrt_nonneg (1 - x ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 - y^2) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x^2) by nlinarith), mul_nonneg (Real.sqrt_nonneg (1 - y^2)) (Real.sqrt_nonneg (1 -x^2))]