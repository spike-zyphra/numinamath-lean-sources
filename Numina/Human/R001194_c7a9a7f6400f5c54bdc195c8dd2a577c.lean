import Mathlib

/- Let $g(2x + 5) = 4x^2 - 3x + 2$. Find $g(-3)$. -/
theorem algebra_21043 {g : ℝ → ℝ} (h : ∀ x, g (2 * x + 5) = 4 * x ^ 2 - 3 * x + 2) :
    g (-3) = 78 := by 
  specialize h (-4)
  norm_num at h ⊢
  linarith