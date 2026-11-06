import Mathlib

theorem algebra_280961 (x : ℝ) (h₀ : ∃ d, [4, 7, 10] = [1 + d, 4 + d, 7 + d]) (h₁ : ∃ d, [25, x, 36] = [4 + d, 7 + d, 10 + d]) :
    x = 37 := by
  rcases h₀ with ⟨d₀, h₀⟩
  rcases h₁ with ⟨d₁, h₁⟩
  norm_num [Prod.ext_iff] at h₀ h₁
  all_goals linarith