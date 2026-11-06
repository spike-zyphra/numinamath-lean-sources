import Mathlib

theorem algebra_122332 (x y : ℝ) (hy : |y| ≤ 1) (hxy : 2 * x + y = 1) :
    2 * x ^ 2 + 16 * x + 3 * y ^ 2 ≥ 3 := by

  have h1 : -1 ≤ y := by linarith [abs_le.mp hy]
  have h2 : y ≤ 1 := by linarith [abs_le.mp hy]

  have h3 : y = 1 - 2 * x := by linarith

  have h4 : 0 ≤ x := by
    nlinarith [h3, h1, h2]

  have h5 : x ≤ 1 := by
    nlinarith [h3, h1, h2]

  nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (y + 1), 
            hxy, hy, abs_le.mp hy]