import Mathlib

theorem inequalities_38367 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hle : x ≤ 1) :
    x * y + y + 2 * z ≥ 4 * Real.sqrt (x * y * z) := by

  have hxyz : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos hx hy
    exact hz
  have h1 : 0 ≤ Real.sqrt (x * y * z) := Real.sqrt_nonneg (x * y * z)
  nlinarith [Real.sqrt_nonneg (x * y * z),
            Real.sq_sqrt (show 0 ≤ (x * y * z : ℝ) by positivity),
            sq_nonneg (x * y - 2 * Real.sqrt (x * y * z)),
            sq_nonneg (y - 2 * Real.sqrt (x * y * z)),
            sq_nonneg (2 * Real.sqrt (x * y * z) - y),
            sq_nonneg (Real.sqrt (x * y * z) ^ 2 - (x * y * z)),
            mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ x by linarith),
            sq_nonneg (z - Real.sqrt (x * y * z)),
            sq_nonneg ((Real.sqrt (x * y * z)) ^ 2 - z),
            sq_nonneg (y * (1 - x)),
            sq_nonneg (x - 1 / 2),
            sq_nonneg (y - 2 * z),
            sq_nonneg (z - y / 2),
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]