import Mathlib

theorem algebra_10972 (r : ℝ) (hr : r > 0) (h : ∀ x y, x ^ 2 + y ^ 2 - 6.5 = x + 3 * y ↔
    (x - 0.5) ^ 2 + (y - 1.5) ^ 2 = r ^ 2) :
    r = 3 := by
  have h1 := h 0.5 (1.5 + r)
  norm_num at h1
  nlinarith [sq_nonneg (r - 3), hr]