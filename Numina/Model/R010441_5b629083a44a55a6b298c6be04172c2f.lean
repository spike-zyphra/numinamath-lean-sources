import Mathlib

theorem algebra_21890 {x y z : ℝ} (hx : x = -2/3) (hy : y = 5/7) (hz : z = -11/13) : x * y / z = 130/231 := by 
  rw [hx, hy, hz]
  norm_num