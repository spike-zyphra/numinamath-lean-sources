import Mathlib

theorem algebra_3643 {f : ℝ → ℝ} (h : ∀ x, f (2*x - 8) = x^4 - 6) : f (-6) = -5 := by
  have h1 := h 1
  norm_num at h1 
  linarith