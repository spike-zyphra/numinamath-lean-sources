import Mathlib

theorem algebra_10887 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + 2 * y = 12) :
    x * y ^ 2 ≤ 64 := by
  have h1 : x = 12 - 2 * y := by linarith
  rw [h1]
  have h2 : (12 - 2 * y) * (y ^ 2) ≤ 64 := by
    nlinarith [sq_nonneg (y - 4), sq_nonneg (y ^ 2 - 16), sq_nonneg (y * (y - 4)), sq_nonneg ((12 - 2 * y) - 4), sq_nonneg (y), sq_nonneg (12 - 2 * y), mul_pos (show 0 < 12 - 2 * y by nlinarith) (show 0 < y by linarith), sq_nonneg (y - 4)]
  nlinarith