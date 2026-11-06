import Mathlib

theorem inequalities_321494 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    1 / x + 4 / y + 9 / z ≥ 36 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  have h2 : 1 / x + 4 / y + 9 / z - 36 ≥ 0 := by
    have h4 : (1 / x + 4 / y + 9 / z - 36) = (y * z + 4 * x * z + 9 * x * y - 36 * x * y * z) / (x * y * z) := by
      field_simp
      <;> ring
    rw [h4]
    have pos1 : 0 < x * y * z := h1
    have h5 : y * z + 4 * x * z + 9 * x * y - 36 * x * y * z ≥ 0 := by
      nlinarith [sq_nonneg (x - y / 2 - z / 3), sq_nonneg (y - 2 * x / 1), sq_nonneg (z - 3 * x / 1), sq_nonneg (y - 2 * z / 3), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, hsum
      ]
    apply div_nonneg
    linarith
    linarith [h1]
  linarith