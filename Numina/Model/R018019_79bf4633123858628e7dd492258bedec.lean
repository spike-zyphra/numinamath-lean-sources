import Mathlib

theorem inequalities_599869 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxi : x < 1) (hyi : y < 1) (hzi : z < 1) :
    x * (1 - y) * (1 - z) + y * (1 - z) * (1 - x) + z * (1 - x) * (1 - y) < 1 := by
  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  have hz1 : 0 < 1 - z := by linarith
  nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos hx hx1, mul_pos hy hy1, mul_pos hz hz1, 
          mul_pos hx1 hy1, mul_pos hx1 hz1, mul_pos hy1 hz1, 
          mul_pos (mul_pos hx hy) hz, 
          mul_pos (mul_pos hx hy) hx1, 
          mul_pos (mul_pos hx hz) hx1, 
          mul_pos (mul_pos hy hz) hx1 
        ]