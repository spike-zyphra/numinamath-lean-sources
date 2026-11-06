import Mathlib

theorem algebra_221739 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : y = x + 3) (h2 : z = x - 2) (h3 : 1 / x + 1 / y + 1 / z = 1 / 4) :
    x = 12 := by
  have hy_eq : y = x + 3 := h1
  have hz_eq : z = x - 2 := h2
  rw [hy_eq, hz_eq] at h3
  have h4 : x > 0 := hx
  have h5 : x + 3 > 0 := by linarith
  have h6 : x - 2 > 0 := by nlinarith [hx]
  field_simp [h4, h5, h6] at h3
  nlinarith [sq_nonneg (x - 12), sq_nonneg (x + 2), sq_nonneg (x - 1)]