import Mathlib 

theorem algebra_10218 {a b r : ℝ} (hr : 0 < r) (h : ∀ x y : ℝ, x ^ 2 - 6 * y - 3 = - y ^ 2 - 4 * x ↔ (x - a) ^ 2 + (y - b) ^ 2 = r ^ 2) :
    a + b + r = 5 := by
  have h1 := h (-2) 7
  norm_num at h1
  have h2 := h (-2) (-1)
  norm_num at h2
  have h3 := h 2 3
  norm_num at h3
  have h4 : b = 3 := by
    nlinarith
  have h5 : a = -2 := by
    rw [h4] at h1 h3
    nlinarith
  have h6 : r = 4 := by
    rw [h4] at h3
    rw [h5] at h3
    nlinarith
  linarith