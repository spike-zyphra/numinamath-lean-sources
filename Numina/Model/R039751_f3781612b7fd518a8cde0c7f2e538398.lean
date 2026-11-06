import Mathlib

open Real

theorem inequalities_228050 (x y : ℝ) :
    -1 / 2 ≤ ((x + y) * (1 - x * y)) / ((1 + x ^ 2) * (1 + y ^ 2)) ∧
    ((x + y) * (1 - x * y)) / ((1 + x ^ 2) * (1 + y ^ 2)) ≤ 1 / 2 := by
  have h1 : 0 < (1 + x^2) * (1 + y^2) := by
    positivity
  constructor
  · -- Proof of -1/2 ≤ (x + y)(1 - x*y)/((1 + x^2)(1 + y^2))
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + y - 1 + x * y), sq_nonneg (x + y + 1 - x * y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y - 1), sq_nonneg (x * y + 1), sq_nonneg (x * y + 1), sq_nonneg (x - y + x * y), sq_nonneg (x + y - 2*x*y)]
  · -- Proof of (x + y)(1 - x*y)/((1 + x^2)(1 + y^2)) ≤ 1/2
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + y - 1 + x * y), sq_nonneg (x + y + 1 - x * y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y - 1), sq_nonneg (x * y + 1), sq_nonneg (x * y + 1), sq_nonneg (x - y + x * y), sq_nonneg (x + y - 2*x*y)]