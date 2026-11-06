import Mathlib

theorem algebra_15621 (r : ℝ) (h : r > 0) (h' : ∀ x y, x ^ 2 + y ^ 2 + 21 = 4 * x + 18 * y →
    (x - 2) ^ 2 + (y - 9) ^ 2 = r ^ 2) :
    r = 8 := by
  have h1 := h' 10 9 (by norm_num)
  norm_num at h1
  nlinarith [h]