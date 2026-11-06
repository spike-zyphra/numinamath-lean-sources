import Mathlib

theorem algebra_221534 : (Real.sqrt (5 + Real.sqrt 3) + Real.sqrt (5 - Real.sqrt 3))^2 = 10 + 2 * Real.sqrt 22 := by
  have h1 : 0 ≤ 5 + Real.sqrt 3 := by
    positivity
  have h2 : 0 ≤ 5 - Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  have h3 : (Real.sqrt (5 + Real.sqrt 3) + Real.sqrt (5 - Real.sqrt 3)) ^ 2
    = (Real.sqrt (5 + Real.sqrt 3)) ^ 2 + (Real.sqrt (5 - Real.sqrt 3)) ^ 2 + 2 * (Real.sqrt (5 + Real.sqrt 3) * Real.sqrt (5 - Real.sqrt 3)) := by
    ring
  have h4 : (Real.sqrt (5 + Real.sqrt 3)) ^ 2 = 5 + Real.sqrt 3 := by
    rw [Real.sq_sqrt]
    linarith [h1]
  have h5 : (Real.sqrt (5 - Real.sqrt 3)) ^ 2 = 5 - Real.sqrt 3 := by
    rw [Real.sq_sqrt]
    linarith [h2]

  have h6 : Real.sqrt (5 + Real.sqrt 3) * Real.sqrt (5 - Real.sqrt 3) = Real.sqrt 22 := by
    have h7 : Real.sqrt (5 + Real.sqrt 3) * Real.sqrt (5 - Real.sqrt 3) = Real.sqrt ((5 + Real.sqrt 3) * (5 - Real.sqrt 3)) := by
      rw [← Real.sqrt_mul (by nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)])]
    have h8 : (5 + Real.sqrt 3) * (5 - Real.sqrt 3) = (22 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    rw [h8] at h7
    linarith [h7, Real.sqrt_nonneg ((5 + Real.sqrt 3) * (5 - Real.sqrt 3)), Real.sqrt_nonneg 22]

  rw [h3, h4, h5, h6]
  nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 22, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 22 by norm_num)]