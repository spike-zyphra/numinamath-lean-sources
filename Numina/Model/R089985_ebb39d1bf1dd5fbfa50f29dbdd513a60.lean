import Mathlib

theorem algebra_193162 (D : ℝ) (h : ∀ x y, x + 2 * y + 1 = 0 → 9 * x + D * y + 1 = 0) :
    D = 18 := by
  have h1 := h (-1) (0) (by norm_num)
  norm_num at h1
  all_goals linarith