import Mathlib

theorem algebra_317085 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = 25 / 4) (h2 : y^2 + y * z + z^2 = 36) (h3 : z^2 + z * x + x^2 = 169 / 4) :
    x * y + y * z + z * x = 10 * Real.sqrt 3 := by
  have h4 : (x * y + y * z + z * x) ^ 2 = 300 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]

  have h5 : x * y + y * z + z * x ≥ 0 := by
    nlinarith

  have h6 : x * y + y * z + z * x = Real.sqrt 300 := by
    have h7 : (x * y + y * z + z * x) ^ 2 = 300 := h4
    have h8 : x * y + y * z + z * x ≥ 0 := h5
    have h9 : (x * y + y * z + z * x) = Real.sqrt 300 := by
      rw [← h7]
      field_simp
    linarith
  have h7 : Real.sqrt 300 = 10 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  rw [h7] at h6
  linarith [h6]