import Mathlib

theorem algebra_40651 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 / 3 = 25) (h2 : y^2 / 3 + z^2 = 9) (h3 : z^2 + z * x + x^2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  have h5 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ 3 by norm_num)
  have h4 : x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
    nlinarith [h1, h2, h3, Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num), Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  exact h4