import Mathlib

theorem algebra_7963 {a b : ℝ} (h : ∀ x, (x^3 + a * x^2 + b * x + 8) % (x^2 + 5 * x + 4) = 0) :
    a + b = 21 := by
  have h1 := h (-1)
  have h2 := h (-4)
  norm_num at h1 h2
  linarith