import Mathlib

theorem algebra_20076 (h l : ℝ) (h₀ : h = l + 16) (h₁ : (h + l) / 2 = 3) :
    l = -5 := by
  have eq1 : h + l = 6 := by 
    linarith
  rw [h₀] at eq1
  linarith