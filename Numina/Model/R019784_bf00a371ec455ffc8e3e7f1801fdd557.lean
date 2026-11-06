import Mathlib

theorem algebra_237374 {x y : ℝ} (hxy : x = y * (3 - y) ^ 2) (hyx : y = x * (3 - x) ^ 2) :
    x + y = 0 ∨ x + y = 3 ∨ x + y = 4 ∨ x + y = 5 ∨ x + y = 8 := by 
  have h1 : (x + y - 0) * (x + y - 3) * (x + y - 4) * (x + y - 5) * (x + y - 8) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - 4), sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (y - 4)]
  cases' (mul_eq_zero.mp h1) with h2 h3
  cases' (mul_eq_zero.mp h2) with h2 h4
  cases' (mul_eq_zero.mp h2) with h2 h5
  cases' (mul_eq_zero.mp h2) with h2 h6
  · -- Case h2 : x + y - 0 = 0
    left
    linarith
  · -- Case h5 : x + y - 3 = 0
    right
    left
    linarith
  · -- Case h4 : x + y - 4 = 0
    right
    right
    left
    linarith
  · -- Case h6 : x + y - 5 = 0
    right
    right
    right
    left
    linarith
  · -- Case h3 : x + y - 8 = 0
    right
    right
    right
    right
    linarith