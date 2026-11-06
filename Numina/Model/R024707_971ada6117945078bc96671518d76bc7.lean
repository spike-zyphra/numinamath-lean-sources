import Mathlib

theorem inequalities_57739 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : Real.sqrt (x * y * z) = x * y + y * z + z * x) : x + y + z ≤ 1 / 3 := by
  have h1 : 0 < x * y * z := by positivity
  have h2 : Real.sqrt (x * y * z) ≥ 0 := by positivity
  have h3 : x * y * z = (x * y + y * z + z * x) ^ 2 := by
    calc
      x * y * z = (Real.sqrt (x * y * z)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (x * y + y * z + z * x) ^ 2 := by
        rw [h]
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            h3, sq_nonneg (x * y * z - 1 / 27),
            sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]