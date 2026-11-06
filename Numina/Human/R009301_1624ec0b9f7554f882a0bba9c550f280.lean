import Mathlib

/- If $g(2x - 5) = 3x + 9$ for all real $x$, then what is $g(1)$? -/
theorem algebra_14414 {g : ℝ → ℝ} (h : ∀ x, g (2 * x - 5) = 3 * x + 9) :
    g 1 = 18 := by
  have h₁ := h 3
  simp at h₁
  norm_num at h₁
  linarith