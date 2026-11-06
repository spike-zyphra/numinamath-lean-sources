import Mathlib

theorem algebra_301189 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^3 + y^3 - 3 * x * y + 1 = 0) :
    x = y ∧ y = 1 := by 
  have h1 : (x + y + 1) * (x^2 + y^2 + 1 - x * y - x - y) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  cases' (mul_eq_zero.1 h1) with h2 h3
  · -- Case where x + y + 1 = 0.
    nlinarith [show x + y ≥ 0 from by linarith, h2]
  · -- Case where x^2 + y^2 + 1 - x * y - x - y = 0.
    have h4 : (y - 1) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1)]
    have hy1 : y = 1 := by 
      nlinarith
    have hx1 : x = 1 := by
      rw [hy1] at h3
      nlinarith [sq_nonneg (x - 1)]
    constructor
    · -- Show x = y.
      nlinarith [hx1, hy1]
    · -- Show y = 1.
      exact hy1