import Mathlib

theorem algebra_296888 (a b : ℝ) (h : a * b = 2 * a + 2 * b - 3) :
    a ^ 2 + b ^ 2 ≥ 2 := by
  have h1 : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by
    nlinarith
  rw [h1, h]
  nlinarith [sq_nonneg (a + b - 2)]