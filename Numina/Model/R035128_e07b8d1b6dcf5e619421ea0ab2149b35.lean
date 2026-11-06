import Mathlib

theorem algebra_239669 (a b c : ℤ) (h₀ : a + b = c) (h₁ : a = 49) (h₂ : b = 35) (h₃ : c = 82) :
    a * b = 1429 := by
  rw [h₁, h₂, h₃] at h₀
  all_goals
    omega