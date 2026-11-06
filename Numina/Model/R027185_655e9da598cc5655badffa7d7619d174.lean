import Mathlib

theorem inequalities_7550 (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) : x * y + y * z + z * t + t * x ≤ (1 / 4) * (x + y + z + t) ^ 2 := by 
  suffices 4 * (x * y + y * z + z * t + t * x) ≤ (x + y + z + t) ^ 2 by
    linarith
  nlinarith [sq_nonneg (x + y - z - t), sq_nonneg (x - y + z - t), sq_nonneg (x - y - z + t), sq_nonneg (x + y - z + t), sq_nonneg (x - y + z + t), sq_nonneg (x - y - z - t), mul_pos hx hy, mul_pos hx hz, mul_pos hx ht, mul_pos hy hz, mul_pos hy ht, mul_pos hz ht]