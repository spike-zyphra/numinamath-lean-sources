import Mathlib

theorem algebra_300406
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = 9)
    (h2 : y^2 + y * z + z^2 = 16)
    (h3 : z^2 + z * x + x^2 = 25) :
    x * y + y * z + z * x = 8 * Real.sqrt 3 := by
  have h4 : (x * y + y * z + z * x) ^ 2 = 192 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
                sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h5 : x * y + y * z + z * x ≥ 0 := by
    nlinarith
  have h6 : x * y + y * z + z * x = Real.sqrt 192 := by
    have h7 : (x * y + y * z + z * x) ≥ 0 := h5
    have h8 : (Real.sqrt 192) ^ 2 = 192 := Real.sq_sqrt (by norm_num)
    have h9 : (x * y + y * z + z * x) ^ 2 = (Real.sqrt 192) ^ 2 := by linarith [h4, h8]
    have h10 : (x * y + y * z + z * x) = Real.sqrt 192 := by
      nlinarith [Real.sqrt_nonneg 192]
    exact h10
  have h7 : Real.sqrt 192 = 8 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num
  rw [h7] at h6
  exact h6