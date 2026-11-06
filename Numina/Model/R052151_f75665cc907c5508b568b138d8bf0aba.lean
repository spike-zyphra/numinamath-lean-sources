import Mathlib

theorem inequalities_92020 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z + x * y + y * z + z * x = 4) : 3 ≤ x + y + z:= by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
]