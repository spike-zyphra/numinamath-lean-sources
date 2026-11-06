import Mathlib

theorem algebra_7221 (x y z : ℝ) (hx : x = -3) (hy : y = -3) (hz : z = 17) :
    Real.sqrt (z - y^2 - 6 * x - 26) + x^2 + 6 * y + z - 8 = 0 := by 
  rw [hx, hy, hz]
  have h1 : Real.sqrt (17 - (-3 : ℝ)^2 - 6 * (-3) - 26) = 0 := by
    rw [Real.sqrt_eq_zero']
    all_goals norm_num
  have h2 : (-3 : ℝ) ^ 2 + 6 * (-3 : ℝ) + 17 - 8 = 0 := by 
    norm_num
  rw [h1]
  linarith [h2]