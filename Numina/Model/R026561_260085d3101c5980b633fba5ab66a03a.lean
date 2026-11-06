import Mathlib

theorem algebra_221414 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x, x * (x + a) = b ^ 2 := by
  use (-a + Real.sqrt (a^2 + 4 * b^2)) / 2
  nlinarith [Real.sqrt_nonneg (a^2 + 4 * b ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 + 4 * b ^ 2 by nlinarith)]