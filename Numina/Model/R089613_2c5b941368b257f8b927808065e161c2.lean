import Mathlib

theorem algebra_168504 {x y : ℝ} (h : 2^2 = x - 2) (h' : 2^3 = 2 * x - y + 1) :
    Real.sqrt (x^2 - 4 * y) = 4 := by
  have hx : x = 6 := by
    linarith
  have hy : y = 5 := by
    rw [hx] at h'
    linarith
  have h1 : x^2 - 4 * y = 16 := by
    rw [hx, hy]
    norm_num
  rw [h1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num