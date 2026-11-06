import Mathlib

theorem algebra_169238 (p1 p2 p3 : ℝ)
    (h₀ : p1 = 20 / 100) (h₁ : p2 = 46 / 100) (h₂ : p3 = 34 / 100)
    (h₃ : (1 - p1) * (1 - p2) * (1 - p3) = (1 - 3 / 100) * (1 - 2 / 100) * (1 - 1 / 100)) :
    (1 - p1) * (1 - p2) * (1 - p3) * p1 = 0.322 := by
  rw [h₀, h₁, h₂] at h₃ ⊢
  norm_num at h₃ ⊢
  all_goals nlinarith