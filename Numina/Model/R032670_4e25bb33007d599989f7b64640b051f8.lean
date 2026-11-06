import Mathlib

theorem algebra_325210 (x y : ℝ) (hx : 0 ≤ x + 2) (hy : 5 ≤ y) (h : Real.sqrt (x + 2) + Real.sqrt (y - 5) = 6) :
    x + 2 * y ≥ 32 ∧ x + 2 * y ≤ 80 := by

  have h1 : 0 ≤ Real.sqrt (x + 2) := by
    apply Real.sqrt_nonneg

  have h2 : 0 ≤ Real.sqrt (y - 5) := by
    apply Real.sqrt_nonneg

  have h3 : Real.sqrt (x + 2) ^ 2 = x + 2 := by
    rw [Real.sq_sqrt]
    linarith

  have h4 : Real.sqrt (y - 5) ^ 2 = y - 5 := by
    rw [Real.sq_sqrt]
    have h5 : 0 ≤ y - 5 := by linarith
    linarith

  have eq1 : x + 2 * y = 3 * (Real.sqrt (x + 2)) ^ 2 - 24 * Real.sqrt (x + 2) + 80 := by
    nlinarith [h3, h4, h]

  have h7 : 0 ≤ Real.sqrt (x + 2) := by
    apply Real.sqrt_nonneg

  have h8 : Real.sqrt (x + 2) ≤ 6 := by
    nlinarith [show 0 ≤ Real.sqrt (y - 5) by positivity, h]

  constructor
  · -- Prove the minimum
    nlinarith [sq_nonneg (Real.sqrt (x + 2) - 4), sq_nonneg (Real.sqrt (x + 2) - 0), sq_nonneg (Real.sqrt (x + 2) - 6), Real.sqrt_nonneg (x + 2)]

  · -- Prove the maximum
    nlinarith [sq_nonneg (Real.sqrt (x + 2) - 0), sq_nonneg (Real.sqrt (x + 2) - 6), Real.sqrt_nonneg (x + 2)]