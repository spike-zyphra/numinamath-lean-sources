import Mathlib

theorem algebra_16414 (d1 d2 v1 v2 : ℝ) (h₁ : d1 = 30) (h₂ : d2 = 10) (h₃ : v1 = 10) (h₄ : v2 = 30) :
    (d1 + d2) / (d1 / v1 + d2 / v2) = 12 := by 
  rw [h₁, h₂, h₃, h₄]
  norm_num