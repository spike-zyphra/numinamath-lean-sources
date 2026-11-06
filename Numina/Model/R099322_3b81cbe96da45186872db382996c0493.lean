import Mathlib

theorem algebra_217408 (a b c d : ℝ) (h₀ : a < b) (h₁ : b < c) (h₂ : c < d)
    (h₃ : a + b + c = 180) (h₄ : a + b + d = 197) (h₅ : a + c + d = 208)
    (h₆ : b + c + d = 222) :
    a + b + c ≠ 208 := by 
  intro h
  have h₇ : a + b + c = 180 := h₃
  linarith