import Mathlib

theorem algebra_8056 {x y : ℝ} (hx : (x - 1)^3 + 2012 * (x - 1) = 1) (hy : (y - 1)^3 + 2012 * (y - 1) = -1) : x + y = 2 := by
  have h1 : (x - 1) ^ 3 + 2012 * (x - 1) + (y - 1) ^ 3 + 2012 * (y - 1) = 0 := by
    linarith [hx, hy]
  have h2 : (x + y - 2) * ((x - 1)^2 + (y - 1)^2 - (x - 1) * (y - 1) + 2012) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1)]
  cases (mul_eq_zero.mp h2) with
  | inl h3 =>
    linarith
  | inr h4 =>
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1)]