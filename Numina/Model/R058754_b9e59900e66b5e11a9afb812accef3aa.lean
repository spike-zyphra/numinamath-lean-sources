import Mathlib

theorem algebra_193298 {x y z : ℝ} (hx : x = 0.8) (hy : y = 0.85) (hz : z = 0.9) :
    (1 - x * y * z) * 100 = 38.8 := by 
  rw [hx, hy, hz]
  norm_num