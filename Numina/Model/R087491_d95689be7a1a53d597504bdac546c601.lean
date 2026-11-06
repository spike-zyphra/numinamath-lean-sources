import Mathlib

theorem algebra_282563 (a b c : ℤ) (h₀ : a = 22) (h₁ : b = a - 19) (h₂ : c = b - 11) :
    c = -8 := by
  rw [h₀] at h₁
  have hb : b = 3 := by
    linarith
  rw [hb] at h₂
  linarith