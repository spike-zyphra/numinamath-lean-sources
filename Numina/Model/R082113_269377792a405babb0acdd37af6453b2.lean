import Mathlib

open Real
open scoped BigOperators

theorem algebra_12166 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
  (h : x * y + y * z + z * x = 24) :
  (1/3) * x * y * z ≤ 16 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          mul_self_nonneg (x - 4), mul_self_nonneg (y - 4), mul_self_nonneg (z - 4)
]