import Mathlib

theorem algebra_11231 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (hxy : x / y = 3 / 2) (harea : (1 / 2) * x * y = 108) :
    max x y = 18 := by
  have h1 : x = (3 / 2) * y := by
    have h2 : y ≠ 0 := by linarith
    field_simp [h2] at hxy
    linarith
  rw [h1] at harea
  have h3 : y^2 = 144 := by
    nlinarith
  have hy_val : y = 12 := by
    nlinarith [h3, hy]
  have hx_val : x = 18 := by
    rw [hy_val] at h1
    nlinarith
  rw [hx_val, hy_val]
  norm_num