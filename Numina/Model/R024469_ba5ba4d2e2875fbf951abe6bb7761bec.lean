import Mathlib

theorem algebra_113046 {x y : ℝ} (h : x^3 + 21*x*y + y^3 = 343) :
    x + y = 7 ∨ x + y = -14 := by
  have h1 : (x + y - 7) * (x + y + 14) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 7), sq_nonneg (x + y + 14),
      sq_nonneg (x - y), sq_nonneg (x + y - 7), sq_nonneg (x + y + 14),
      sq_nonneg (x + y)]
  cases' (mul_eq_zero.1 h1) with h2 h3
  · -- Case where $x + y - 7 = 0$, which means $x + y = 7$, the first possibility.
    left
    linarith
  · -- Case where $x + y + 14 = 0$, which means $x + y = -14$, the second possibility.
    right
    linarith