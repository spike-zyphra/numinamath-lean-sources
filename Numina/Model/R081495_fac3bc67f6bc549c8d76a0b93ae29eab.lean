import Mathlib

theorem number_theory_7909 (a b : ℕ) (h₀ : a^2 + b^2 = b^2 + 2 * b + 1) (h₁ : b < 100) :
    a ≤ 14 := by 
  have h2 : a^2 = 2 * b + 1 := by
    nlinarith
  have h3 : b < 100 := h₁
  have h4 : 2 * b + 1 < 201 := by 
    omega
  have h5 : a^2 < 201 := by 
    linarith [h2, h4]
  nlinarith [show a ≤ 14 by nlinarith [h5]]