import Mathlib

theorem algebra_598917 (x y z r : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hr : 0 < r)
    (h1 : z * Real.sqrt (x ^ 2 - r ^ 2) = x ^ 2) (h2 : x * y = r * z) :
    x ^ 2 + y ^ 2 = z ^ 2 := by
  have h3 : x ^ 2 - r ^ 2 ≥ 0 := by
    by_contra h
    push_neg at h
    have h4 : Real.sqrt (x ^ 2 - r ^ 2) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      nlinarith
      all_goals linarith
    rw [h4] at h1
    nlinarith
  have h4 : (z * Real.sqrt (x ^ 2 - r ^ 2)) ^ 2 = (x ^ 2) ^ 2 := by
    rw [h1]
  have h5 : (z * Real.sqrt (x ^ 2 - r ^ 2)) ^ 2 = z ^ 2 * (x ^ 2 - r ^ 2) := by
    calc
      (z * Real.sqrt (x ^ 2 - r ^ 2)) ^ 2 = z ^ 2 * (Real.sqrt (x ^ 2 - r ^ 2) ^ 2) := by ring
      _ = z ^ 2 * (x ^ 2 - r ^ 2) := by
        rw [Real.sq_sqrt]
        linarith
  have h6 : (x ^ 2) ^ 2 = x ^ 4 := by ring
  have h7 : z ^ 2 * (x ^ 2 - r ^ 2) = x ^ 4 := by
    linarith [h4, h5, h6]
  have h8 : r = (x * y) / z := by
    have h9 : z ≠ 0 := by linarith
    field_simp at *
    nlinarith [h2]
  have h9 : z ^ 2 * (x ^ 2 - r ^ 2) = x ^ 4 := h7
  rw [show r = (x * y) / z by linarith [h8]] at h9
  have h11 : z ^ 2 * (x ^ 2 - ((x * y) / z) ^ 2) = x ^ 2 * (z ^ 2 - y ^ 2) := by
    field_simp
    <;> nlinarith
  have h12 : x ^ 2 * (z ^ 2 - y ^ 2) = x ^ 4 := by
    linarith [h11, h9]
  have h13 : z ^ 2 - y ^ 2 = x ^ 2 := by
    have hx2_ne_zero : x ^ 2 ≠ 0 := by
      nlinarith
    apply (mul_left_inj' hx2_ne_zero).mp
    linarith
  linarith [h13]