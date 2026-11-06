import Mathlib

theorem algebra_218096 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / v = d / (v + w) + 50 / 60) (h₃ : d / v = d / (w + v) + 10 / 60)
    (h₄ : d / v = d / (v + w) + 1.5) :
    d / v = 3 := by
  have h₅ : d / (v + w) + 10 / 60 = d / (v + w) + 1.5 := by
    linarith
  have h₆ : (10 / 60 : ℝ) = 1.5 := by
    linarith
  norm_num at h₆
  all_goals try contradiction