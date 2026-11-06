import Mathlib

theorem algebra_4402 {g : ℝ → ℝ} (h : ∀ x, g (2 * x - 5) = 3 * x + 9) :
    g 1 = 18 := by 
  have h3 := h 3
  norm_num at h3 
  linarith