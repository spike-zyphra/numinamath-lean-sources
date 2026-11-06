import Mathlib

open Real

theorem inequalities_5774 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxyz : x * y + y * z + z * x + x * y * z = 4) :
    x * y * z ≤ 1 := by 
  nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
    sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
    mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]