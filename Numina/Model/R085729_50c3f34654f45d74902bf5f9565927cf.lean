import Mathlib

theorem algebra_277144 (a b c d e f g h i j : ℝ)
    (h₀ : (a + b + c + d) / 4 = 95)
    (h₁ : (e + f + g + h + i + j) / 6 = (a + b + c + d + e + f + g + h + i + j) / 10 - 6) :
    (a + b + c + d + e + f + g + h + i + j) / 10 = 86 := by
  have h2 : a + b + c + d = 380 := by
    linarith
  have h3 : e + f + g + h + i + j = (3 / 5) * (a + b + c + d + e + f + g + h + i + j) - 36 := by
    linarith
  have h4 : a + b + c + d + e + f + g + h + i + j = 860 := by
    linarith [h2, h3]
  linarith [h4]