import Mathlib

theorem algebra_147372 (a b : ℝ) (ha : a^3-3*a^2+5*a-17=0) (hb : b^3-3*b^2+5*b+11=0) :
    a+b ≤ 4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 4), sq_nonneg (a - 2), sq_nonneg (b - 2),
          sq_nonneg (a - 4 + b), sq_nonneg (a - b)]