import Mathlib

theorem algebra_327620 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + 2 * y = 2) :
    x ^ 2 / (2 * y) + 4 * y ^ 2 / x ≥ 2 := by
  have h1 : 0 < 2 * x * y := by
    nlinarith [hx, hy]

  have h2 : x ^ 2 / (2 * y) + 4 * y ^ 2 / x - 2 ≥ 0 := by
    have h3 : x ^ 2 / (2 * y) + 4 * y ^ 2 / x - 2 = (x ^ 3 + 8 * y ^ 3 - 4 * x * y) / (2 * x * y) := by
      field_simp
      ring
    rw [h3]
    have h4 : x ^ 3 + 8 * y ^ 3 - 4 * x * y ≥ 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1 / 2), sq_nonneg (2 * y - 1), sq_nonneg (x + 2 * y - 2), sq_nonneg (x - 2 * y), sq_nonneg (x ^ 2 - 1), sq_nonneg ((2 * y) ^ 2 - 1), h, mul_pos hx hy, sq_nonneg (x * y)]
    have h5 : 0 < (2 * x * y : ℝ) := by nlinarith
    exact div_nonneg h4 (by positivity)
  linarith