import Mathlib

theorem algebra_237932 {x y : ℝ} (h₁ : (x - 1)^3 + 1997 * (x - 1) = -1) (h₂ : (y - 1)^3 + 1997 * (y - 1) = 1) :
    x + y = 2 := by
  have h3 : (x - 1)^3 + 1997 * (x - 1) + (y - 1)^3 + 1997 * (y - 1) = 0 := by
    linarith
  have h4 : (x - 1 + y - 1) * ((x - 1)^2 + (y - 1)^2 - (x - 1) * (y - 1) + 1997) = 0 := by
    nlinarith [sq_nonneg (x - 1 - (y - 1)), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- Case where x - 1 + y - 1 = 0
    linarith
  · -- Case where (x - 1)^2 + (y - 1)^2 - (x - 1) * (y - 1) + 1997 = 0
    nlinarith [sq_nonneg (x - 1 - (y - 1)), sq_nonneg (x - 1), sq_nonneg (y - 1)]