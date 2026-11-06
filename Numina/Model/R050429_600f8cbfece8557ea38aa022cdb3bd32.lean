import Mathlib

theorem inequalities_602228
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) ≥ x + y + z := by
  have pos1 : 0 < y * z := mul_pos hy hz
  have pos2 : 0 < z * x := mul_pos hz hx
  have pos3 : 0 < x * y := mul_pos hx hy
  have h1 : x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) - (x + y + z) ≥ 0 := by
    have pos4 : 0 < (x * y * z) := mul_pos (mul_pos hx hy) hz
    have h2 : x ^ 3 / (y * z) + y ^ 3 / (z * x) + z ^ 3 / (x * y) - (x + y + z) =
      (x ^ 4 + y ^ 4 + z ^ 4 - (x ^ 2 * y * z + x * y ^ 2 * z + x * y * z ^ 2)) / (x * y * z) := by
      field_simp [show y ≠ 0 by linarith, show z ≠ 0 by linarith, show x ≠ 0 by linarith]
      ring
    rw [h2]
    apply div_nonneg
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (z ^ 2 - x ^ 2), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x^2 - y * z), sq_nonneg (y^2 - x * z), sq_nonneg (z^2 - x * y), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    positivity
  linarith