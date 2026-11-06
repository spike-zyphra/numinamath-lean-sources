import Mathlib

theorem algebra_609814 {x y z : ℝ} (hx : x * (7 / 5) + 16 = x) (hy : (7 * y - 80) / 9 = y) (hz : z * (7 / 5) + 16 = (7 * z - 80) / 9) :  x + y + z = -120 := by
  have hx_val : x = -40 := by
    linarith
  have hy_val : y = -40 := by
    linarith
  have hz_val : z = -40 := by
    linarith
  linarith [hx_val, hy_val, hz_val]