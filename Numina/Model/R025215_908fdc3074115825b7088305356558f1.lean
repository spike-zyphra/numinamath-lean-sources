import Mathlib

theorem inequalities_601374 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxi : x < 1) (hyi : y < 1) (hyi' : z < 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - x) < 1 := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 1 - y := by linarith
  have h3 : 0 < 1 - z := by linarith
  nlinarith [mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
            mul_pos h1 h2, mul_pos h2 h3, mul_pos h3 h1, 
            mul_pos h1 h2, mul_pos h2 h3, mul_pos h3 h1, 
            mul_pos hx h1, mul_pos hy h2, mul_pos hz h3]