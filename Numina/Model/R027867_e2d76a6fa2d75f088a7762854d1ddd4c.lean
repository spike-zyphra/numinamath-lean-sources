import Mathlib

theorem algebra_50352 {x y z : ℝ}
    (h1 : x^2 - 2 * x - 4 * z = 3) (h2 : y^2 - 2 * y - 2 * x = -14) (h3 : z^2 - 4 * y - 4 * z = -18) :
    (x, y, z) = (2, 3, 4) := by
  have h4 : (x - 2) ^ 2 + (y - 3) ^ 2 + (z - 4) ^ 2 = 0 := by
    nlinarith
  have hx1 : (x - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (z - 4)]
  have hy1 : (y - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (z - 4)]
  have hz1 : (z - 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (z - 4)]
  have hx2 : x - 2 = 0 := by
    rwa [sq_eq_zero_iff] at hx1
  have hy2 : y - 3 = 0 := by
    rwa [sq_eq_zero_iff] at hy1
  have hz2 : z - 4 = 0 := by
    rwa [sq_eq_zero_iff] at hz1
  have h5 : x = 2 := by linarith
  have h6 : y = 3 := by linarith
  have h7 : z = 4 := by linarith
  simp [Prod.ext_iff, h5, h6, h7]