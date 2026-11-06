import Mathlib

theorem algebra_291827 (a : ℕ → ℤ) (h₀ : a 0 = 0) (h₁ : a 1 = a 0 + 2) (h₂ : a 2 = a 1 + 4)
    (h₃ : a 3 = a 2 - 1) (h₄ : a 4 = a 3 + 0) (h₅ : a 5 = a 4 - 5) (h₆ : a 6 = a 5 - 3)
    (h₇ : a 7 = a 6 + 3) : a 7 = 0 + (2 + 4 - 1 + 0 - 5 - 3 + 3) := by
  have ha1 : a 1 = 2 := by
    linarith [h₀, h₁]

  have ha2 : a 2 = 6 := by 
    linarith [ha1, h₂]

  have ha3 : a 3 = 5 := by 
    linarith [ha2, h₃]

  have ha4 : a 4 = 5 := by 
    linarith [ha3, h₄]

  have ha5 : a 5 = 0 := by 
    linarith [ha4, h₅]

  have ha6 : a 6 = -3 := by 
    linarith [ha5, h₆]

  have ha7 : a 7 = 0 := by 
    linarith [ha6, h₇]

  linarith [ha7]