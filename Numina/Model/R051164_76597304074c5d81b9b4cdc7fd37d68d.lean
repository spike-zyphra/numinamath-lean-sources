import Mathlib

theorem algebra_332 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x + y + z = 5) (h2 : 1 / x + 1 / y + 1 / z = 5) (h3 : x * y * z = 1) :
    x ^ 2 + y ^ 2 + z ^ 2 = 15 := by
  have h4 : y * z + x * z + x * y = 5 := by
    field_simp [hx, hy, hz] at h2
    nlinarith [h3, h2]
  have h5 : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (y * z + x * z + x * y) := by
    ring
  rw [h5, h1, h4]
  norm_num