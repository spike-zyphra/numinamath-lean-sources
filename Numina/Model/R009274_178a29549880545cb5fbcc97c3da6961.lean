import Mathlib

theorem algebra_12820 (a r : ℚ) (hr : r ≠ 0) (h₀ : a = 5 / 6) (h₁ : a * r = -4 / 9) (h₂ : a * r ^ 2 = 32 / 135) :
    r = -8 / 15 := by 
  rw [h₀] at h₁ h₂ 
  linarith