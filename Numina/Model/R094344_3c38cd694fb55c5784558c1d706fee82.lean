import Mathlib

theorem algebra_203163 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h1 : x + y = 17) (h2 : x * y = 17) :
    (x ^ 2 - 17 * x) * (y + 17 / y) = -289 := by
  have h3 : 17 / y = x := by
    field_simp [hy]
    nlinarith [h2]
  have h4 : y + 17 / y = 17 := by
    have h3' : 17 / y = x := by
      field_simp [hy]
      nlinarith [h2]
    linarith [h1, h3']
  have h5 : x ^ 2 - 17 * x = -17 := by
    have h6 : y = 17 - x := by linarith [h1]
    rw [h6] at h2
    nlinarith
  rw [h4, h5]
  norm_num