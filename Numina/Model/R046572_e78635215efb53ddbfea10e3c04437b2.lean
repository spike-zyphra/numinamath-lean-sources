import Mathlib

theorem algebra_190922 {a b : ℝ} (h : a^3 - b^3 - a^2 + b^2 + a - b = 0) :
    b = a := by
  have eq1 : (a - b) * (a^2 + a * b + b^2 - (a + b) + 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq1) with h1 h2
  · -- Case where a - b = 0, so b = a.
    linarith
  · -- Case where the quadratic factor is zero.
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a + b)]