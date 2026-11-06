import Mathlib

theorem algebra_187221 {x y : ℝ} (h1 : x + y = 5) (h2 : x + y + x ^ 2 * y + x * y ^ 2 = 24) :
    x ^ 3 + y ^ 3 = 68 := by
  have eq1 : x ^ 2 * y + x * y ^ 2 = 19 := by
    have h2' : x + y + x ^ 2 * y + x * y ^ 2 = 24 := h2
    rw [h1] at h2'
    linarith
  have eq2 : x * y = 19 / 5 := by
    have eq1' : x ^ 2 * y + x * y ^ 2 = 19 := eq1
    have h1' : x + y = 5 := h1
    have eq3 : x ^ 2 * y + x * y ^ 2 = x * y * (x + y) := by
      ring
    rw [eq3] at eq1'
    rw [h1'] at eq1'
    linarith
  have h3 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
    ring
  rw [h3, h1, eq2]
  norm_num