import Mathlib

theorem algebra_601898 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 / x - 1 / y = 1) : x - y ≤ 4 := by
  have h1 : y - x = x * y := by
    field_simp at h
    nlinarith
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y),
          mul_pos hx hy, sq_nonneg (x * y - 1 / 4)]