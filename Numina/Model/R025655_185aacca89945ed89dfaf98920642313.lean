import Mathlib

open Real

theorem algebra_254930 {f : ℝ → ℝ}
    (h₀ : ∀ x, f (-x + 1) = 2 - f (x - 1))
    (h₁ : ∀ x, f (-x - 1) = 2 + f (x - 1))
    (h₂ : ∀ x ∈ Set.Ioo 0 1, f x = logb 2 (x + 1)) :
    f (logb 2 10) = 17 / 5 := by 
  have h3 := h₁ 0
  norm_num at h3 
  all_goals linarith