import Mathlib

theorem algebra_230083 (h1 h2 : ℝ) (h₀ : 0 < h1) (h₁ : 0 < h2)
    (h₂ : h1 / 6 = h2 / 8) (h₃ : (h1 - 3) / 6 = (h2 - 3) / 8) :
    h1 / h2 = 5 / 4 := by 
  have h4 : h1 = 3 / 4 * h2 := by 
    nlinarith 
  nlinarith [h₀, h₁]