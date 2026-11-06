import Mathlib

theorem algebra_18868 (A B C D E : ℝ)
    (h₀ : A = 0) (h₁ : B = 20) (h₂ : C = (B + D) / 2)
    (h₃ : D = 30) (h₄ : E = 40) :
    C - A = 25 := by 
  rw [h₀]
  rw [h₂, h₁, h₃]
  norm_num