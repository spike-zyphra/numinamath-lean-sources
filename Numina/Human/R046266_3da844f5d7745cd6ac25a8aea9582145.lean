import Mathlib

theorem inequalities_603436 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x * y ≥ 1) :
    x ^ 3 + y ^ 3 + 4 * x * y ≥ x ^ 2 + y ^ 2 + x + y + 2 ∧
    2 * (x ^ 3 + y ^ 3 + x * y + x + y) ≥ 5 * (x ^ 2 + y ^ 2) := by 
  constructor
  · nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1),
      mul_self_nonneg (x - y), hxy, mul_pos hx hy, le_of_lt hx, le_of_lt hy]
  · nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1),
      mul_self_nonneg (x - y), hxy, mul_pos hx hy, le_of_lt hx, le_of_lt hy]