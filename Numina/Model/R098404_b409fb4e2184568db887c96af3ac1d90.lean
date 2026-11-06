import Mathlib

theorem algebra_250047 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x * (x + y + z) = 26) (h2 : y * (x + y + z) = 27) (h3 : z * (x + y + z) = 28) :
    (x, y, z) = (26 / 9, 3, 28 / 9) := by

  have h4 : x + y + z > 0 := by linarith

  have h5 : (x + y + z) ^ 2 = 26 + 27 + 28 := by
    nlinarith

  have h5_simp : (x + y + z) ^ 2 = 81 := by
    norm_num at h5 ⊢
    linarith

  have h6 : x + y + z = 9 := by
    nlinarith [sq_nonneg (x + y + z)]

  have hx_eq : x = 26 / 9 := by
    rw [h6] at h1
    linarith

  have hy_eq : y = 3 := by
    rw [h6] at h2
    linarith

  have hz_eq : z = 28 / 9 := by
    rw [h6] at h3
    linarith

  simp [hx_eq, hy_eq, hz_eq]