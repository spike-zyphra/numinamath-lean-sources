import Mathlib

theorem inequalities_601655 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    (1 + x + y)^2 + (1 + y + z)^2 + (1 + z + x)^2 ≥ 27 := by

  have h1 : 0 < x * y := by
    nlinarith

  have h2 : 0 < y * z := by
    nlinarith

  have h3 : 0 < z * x := by
    nlinarith
  have h4 : (1 + x + y)^2 + (1 + y + z)^2 + (1 + z + x)^2 ≥ 27 := by
    nlinarith [sq_nonneg (x + y + z - 3), 
          sq_nonneg (x * y + y * z + z * x - 3), 
          sq_nonneg (x * y * z - 1), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < z by linarith)
        ]
  linarith