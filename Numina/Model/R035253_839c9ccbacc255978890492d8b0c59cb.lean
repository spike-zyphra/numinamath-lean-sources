import Mathlib

theorem inequalities_8564 (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) :
    x * y * z * t / ((x + y) * (z + t)) ≤ ((x + z) ^ 2 * (y + t) ^ 2) / (4 * (x + y + z + t) ^ 2) := by
  have pos1 : 0 < (x + y) * (z + t) := by positivity
  have pos2 : 0 < 4 * (x + y + z + t) ^ 2 := by positivity
  suffices x * y * z * t * (4 * (x + y + z + t) ^ 2) ≤ (x + z) ^ 2 * (y + t) ^ 2 * ((x + y) * (z + t)) by
    have h : x * y * z * t / ((x + y) * (z + t)) ≤ ((x + z) ^ 2 * (y + t) ^ 2) / (4 * (x + y + z + t) ^ 2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (x - z), sq_nonneg (y - t), sq_nonneg (x + z - (y + t)), sq_nonneg (x * t - y * z), 
          sq_nonneg (x * (y + t) - z * (t + y)), sq_nonneg (t * (x + z) - y * (z + x)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hx ht, mul_pos hy hz, mul_pos hy ht, mul_pos hz ht, 
          mul_pos (mul_pos hx hz) (mul_pos hy ht), sq_nonneg (x * y + z * t - x * t - y * z), 
          mul_nonneg (mul_nonneg (le_of_lt hx) (le_of_lt hz)) (mul_nonneg (le_of_lt hy) (le_of_lt ht))]
    exact h
  nlinarith [sq_nonneg (x - z), sq_nonneg (y - t), sq_nonneg (x + z - (y + t)), sq_nonneg (x * t - y * z), 
          sq_nonneg (x * (y + t) - z * (t + y)), sq_nonneg (t * (x + z) - y * (z + x)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hx ht, mul_pos hy hz, mul_pos hy ht, mul_pos hz ht, 
          mul_pos (mul_pos hx hz) (mul_pos hy ht), sq_nonneg (x * y + z * t - x * t - y * z), 
          mul_nonneg (mul_nonneg (le_of_lt hx) (le_of_lt hz)) (mul_nonneg (le_of_lt hy) (le_of_lt ht))]