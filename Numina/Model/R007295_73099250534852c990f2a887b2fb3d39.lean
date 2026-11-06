import Mathlib

theorem algebra_11690 (r s : ℝ) (h : ∀ x, 9 * x ^ 2 - 18 * x - 720 = 0 ↔ (x + r) ^ 2 = s) :
    s = 81 := by
  have h1 := h 10
  have h2 := h (-8)
  norm_num at h1 h2
  nlinarith