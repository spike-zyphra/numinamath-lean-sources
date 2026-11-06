import Mathlib

open Real

theorem inequalities_598903 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = sqrt (x * y * z)) :
    x * y + y * z + z * x ≥ 9 * (x + y + z) := by 
  have h1 : (x + y + z) ^ 2 = x * y * z := by
    calc
      (x + y + z) ^ 2 = (sqrt (x * y * z)) ^ 2 := by rw [h]
      _ = x * y * z := by
        apply sq_sqrt
        positivity
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * y - 9 * x), sq_nonneg (y * z - 9 * y), sq_nonneg (z * x - 9 * z),
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h1]