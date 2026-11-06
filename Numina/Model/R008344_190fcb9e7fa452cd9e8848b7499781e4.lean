import Mathlib

theorem algebra_12590 (a b c d e : ℝ) (h₀ : (a + b + c + d + e) / 5 = 54) (h₁ : (a + b) / 2 = 48) :
    (c + d + e) / 3 = 58 := by
  have h2 : a + b + c + d + e = 270 := by
    linarith
  have h3 : a + b = 96 := by
    linarith
  have h4 : c + d + e = 174 := by
    linarith [h2, h3]
  linarith [h4]