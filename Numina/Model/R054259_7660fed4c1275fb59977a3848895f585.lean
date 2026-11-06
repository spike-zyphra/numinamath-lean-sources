import Mathlib

theorem algebra_216357 {α : ℝ} (hα : α > 0) (h : ∀ p, (150 - p) * α = 100 * (3 * p - 10)) :
    α = 1.4 := by
  have h1 := h 0
  norm_num at h1
  nlinarith