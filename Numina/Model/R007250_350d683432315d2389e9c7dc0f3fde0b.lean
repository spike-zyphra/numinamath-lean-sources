import Mathlib

theorem algebra_98485 {f : ℝ → ℝ} (h : ∀ x, f (3 * x - 1) = x ^ 2 + x + 1) : f 5 = 7 := by 
  have eqn := h 2
  norm_num at eqn 
  linarith