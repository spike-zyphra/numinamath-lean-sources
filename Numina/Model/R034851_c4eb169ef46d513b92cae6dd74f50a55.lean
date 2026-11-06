import Mathlib


theorem algebra_151636 {F : ℝ → ℝ} (hF : ∀ x, F ((1 - x) / (1 + x)) = x) :
    F (-2 - x) = -2 - F x := by
  have h1 := hF 1
  have h2 := hF (-1)
  norm_num at h1 h2
  linarith