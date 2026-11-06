import Mathlib

theorem algebra_326651 {x y : ℝ} (h1 : x + y = 2) (h2 : x^2 + y^2 = 5 / 2) :
    x^4 + y^4 = 41 / 8 := by
  have h3 : x * y = 3 / 4 := by
    have h4 : (x + y) ^ 2 = 4 := by
      rw [h1]
      norm_num
    have h5 : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * (x * y) := by
      ring
    rw [h5] at h4
    rw [h2] at h4
    linarith
  have h6 : x^4 + y^4 = (x^2 + y^2) ^ 2 - 2 * (x * y) ^ 2 := by
    ring
  rw [h6, h2, h3]
  norm_num