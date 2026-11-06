import Mathlib

theorem algebra_213517 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = 9) (h2 : y^2 + y * z + z^2 = 16) (h3 : z^2 + z * x + x^2 = 25) :
    x * y + y * z + z * x = 8 * Real.sqrt 3 := by

  have h7 : (x * y + y * z + z * x)^2 = 192 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h8 : (x * y + y * z + z * x) = Real.sqrt 192 := by
    have h9 : 0 ≤ x * y + y * z + z * x := by
      nlinarith [show 0 < x by linarith, show 0 < y by linarith, show 0 < z by linarith]
    have h10 : (x * y + y * z + z * x) ^ 2 = 192 := h7
    have h11 : Real.sqrt ((x * y + y * z + z * x) ^ 2) = Real.sqrt 192 := by
      rw [h10]
    have h12 : Real.sqrt ((x * y + y * z + z * x) ^ 2) = x * y + y * z + z * x := by
      rw [Real.sqrt_sq (by linarith)]
    linarith [h12, h11]
  have h9 : Real.sqrt 192 = 8 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num [Real.sq_sqrt]
  rw [h8, h9]