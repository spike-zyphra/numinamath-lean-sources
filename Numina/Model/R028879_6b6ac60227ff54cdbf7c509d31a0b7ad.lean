import Mathlib

theorem algebra_20921 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x^2 + y^2 = 1) (h2 : x^4 + y^4 = 17 / 18) : x * y = 1 / 6 := by
  have h3 : (x^2 + y^2) ^ 2 = 1 := by
    rw [h1]
    all_goals norm_num
  have h4 : x^4 + y^4 + 2 * (x * y) ^ 2 = 1 := by
    have h5 : (x^2 + y^2) ^ 2 = x^4 + y^4 + 2 * (x * y) ^ 2 := by
      ring_nf
    rw [h1] at h5
    linarith
  have h5 : (x * y) ^ 2 = 1 / 36 := by
    nlinarith [h2, h4]
  have h6 : x * y > 0 := by
    nlinarith
  have h7 : x * y = 1 / 6 := by
    nlinarith [h5, h6]
  exact h7