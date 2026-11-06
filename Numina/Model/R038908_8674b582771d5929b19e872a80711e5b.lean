import Mathlib

theorem algebra_320849 (a b : ℝ) (h : 6^2 = a * 6 + b) (h' : ∀ x, x^2 = a * x + b → |x| < 2) :
    ∃ x, x^2 - 12 * x + 36 = b ∧ 2 < x ∧ x < 4 := by

  have h1 := h' 6 (by linarith)
  have h2 : |(6 : ℝ)| = 6 := by
    norm_num [abs_of_nonneg]

  rw [h2] at h1
  norm_num at h1