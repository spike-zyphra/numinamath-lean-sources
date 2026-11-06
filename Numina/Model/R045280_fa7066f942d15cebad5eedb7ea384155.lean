import Mathlib

open Real

theorem inequalities_149323 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) / 2 ≥ sqrt (x * y) := by
  have h1 : (sqrt (x * y)) ^ 2 = x * y := by
    rw [Real.sq_sqrt]
    nlinarith
  have h2 : ((x + y) / 2) ^ 2 ≥ (sqrt (x * y)) ^ 2 := by
    have h3 : ((x + y) / 2) ^ 2 ≥ x * y := by
      nlinarith [sq_nonneg (x - y)]
    have h4 : (sqrt (x * y)) ^ 2 = x * y := h1
    nlinarith [h4]
  have h3 : 0 ≤ (x + y) / 2 := by
    linarith [hx, hy]
  have h4 : 0 ≤ sqrt (x * y) := by
    apply Real.sqrt_nonneg
  nlinarith [h2, h3, h4, Real.sqrt_nonneg (x * y)]