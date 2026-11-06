import Mathlib

theorem algebra_148336 (d : ℝ) (h₀ : d / 75 + d / 145 = 4 * 60 + 48) (h₁ : d / 100 + d / 70 = 2 * 60 + 0) :
    d = 290 := by
  exfalso
  norm_num at h₀ h₁ ⊢
  all_goals
    nlinarith