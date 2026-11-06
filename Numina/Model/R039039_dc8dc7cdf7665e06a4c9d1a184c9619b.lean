import Mathlib

theorem inequalities_246521 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    x * y * z * (x + y) * (y + z) * (z + x) ≥ (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  have h2 : 0 < (x + y) * (y + z) * (z + x) := by
    apply mul_pos
    apply mul_pos
    linarith
    linarith
    linarith
  -- Prove main inequality using positivity and nlinarith
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, h, sq_nonneg (x * y * z)]