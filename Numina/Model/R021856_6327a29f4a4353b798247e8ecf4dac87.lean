import Mathlib

theorem inequalities_601316
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h : x^2 + y^2 + z^2 + 9 = 4 * (x + y + z)) :
    x^4 + y^4 + z^4 + 16 * (x^2 + y^2 + z^2) ≥
    8 * (x^3 + y^3 + z^3) + 27 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
          sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
]