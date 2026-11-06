import Mathlib

theorem inequalities_224743 (x y : ℝ) :
    (x + y) / 2 * (x ^ 2 + y ^ 2) / 2 * (x ^ 3 + y ^ 3) / 2 ≤ (x ^ 6 + y ^ 6) / 2 := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - x * y), sq_nonneg (x * y - y ^ 2), sq_nonneg (x ^ 2 * y ^ 2), sq_nonneg (x - y), sq_nonneg (x ^ 2 - 2 * x * y + y ^ 2), sq_nonneg (x ^ 2 + y ^ 2 - 2 * x * y), sq_nonneg (x * y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x + y - 2 * y), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 2 * (x - y)), sq_nonneg (y ^ 2 * (x - y)), sq_nonneg (x * y * (x - y)), sq_nonneg (x * (x - y)), sq_nonneg (y * (x - y)), sq_nonneg (x ^ 2 * y ^ 2 - x ^ 2 * y * (x * y)), sq_nonneg (x^2 - 2*x*y + y^2), sq_nonneg (x^2 + y^2 - x*y), sq_nonneg (x*y - (x + y)/2) ]