import Mathlib

theorem algebra_160327 (a b : ℝ) (h : ¬∃ x y, y = x^2 + a * x + b ∧ x = y^2 + a * y + b) :
    b > 0 := by
  by_contra h1
  push_neg at h1
  have h2 : ∃ x y, y = x^2 + a * x + b ∧ x = y^2 + a * y + b := by
    have h3 : (a - 1) ^ 2 - 4 * b ≥ 0 := by nlinarith [sq_nonneg (a - 1), h1]
    use (1 - a + Real.sqrt ((a - 1) ^ 2 - 4 * b)) / 2,
      (1 - a + Real.sqrt ((a - 1) ^ 2 - 4 * b)) / 2
    constructor
    · -- Show y = x^2 + a * x + b
      nlinarith [Real.sqrt_nonneg ((a - 1) ^ 2 - 4 * b), Real.sq_sqrt (show (0 : ℝ) ≤ (a - 1) ^ 2 - 4 * b by linarith)]
    · -- Show x = y^2 + a * y + b
      nlinarith [Real.sqrt_nonneg ((a - 1) ^ 2 - 4 * b), Real.sq_sqrt (show (0 : ℝ) ≤ (a - 1) ^ 2 - 4 * b by linarith)]
  contradiction