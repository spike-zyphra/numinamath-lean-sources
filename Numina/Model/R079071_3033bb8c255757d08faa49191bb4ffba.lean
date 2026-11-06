import Mathlib

theorem algebra_180288 (a : ℝ) :
    (∀ x : ℝ, 0 ≤ (a + 1) * x^2 - 2 * (a - 1) * x + 3 * a - 3) ↔
    1 ≤ a := by
  constructor
  · -- Assume that the quadratic is non-negative for all real numbers, prove 1 ≤ a
    intro h
    specialize h 0
    nlinarith
  · -- Assume 1 ≤ a, prove the quadratic is non-negative for all real numbers x
    intro ha x
    nlinarith [sq_nonneg ((a + 1) * x - (a - 1)), sq_nonneg (x - ( (a - 1) / (a + 1)) ), sq_nonneg (x - 1), sq_nonneg (a - 1), mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ a + 1 by linarith)]