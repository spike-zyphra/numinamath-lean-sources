import Mathlib

theorem inequalities_159677 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1) : x + y ≥ 2 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), mul_pos hx hy]