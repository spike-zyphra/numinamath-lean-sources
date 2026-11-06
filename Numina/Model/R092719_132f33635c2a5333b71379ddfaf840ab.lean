import Mathlib

theorem algebra_111584 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x * y = 1) :
    x ^ 4 + y ^ 4 + x ^ 2 + y ^ 2 + Real.sqrt (2 * x * y) ≥ 4 + Real.sqrt 2 := by
  have h1 : Real.sqrt (2 * x * y) = Real.sqrt 2 := by
    have h2 : 2 * x * y = 2 := by
      nlinarith [hxy]
    rw [h2]
  rw [h1]
  have h2 : x ^ 2 + y ^ 2 ≥ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1)]
  have h3 : x ^ 4 + y ^ 4 ≥ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1)]
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h2, h3]