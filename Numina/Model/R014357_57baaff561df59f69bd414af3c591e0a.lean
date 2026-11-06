import Mathlib

theorem number_theory_299422 (a b c d : ℕ) (h₀ : a < 10) (h₁ : b < 10) (h₂ : c < 10) (h₃ : d < 10)
    (h₄ : (1000 * a + 100 * b + 10 * c + d) - (100 * a + 10 * b + c) - (10 * a + b) - a = 1995) :
    (1000 * a + 100 * b + 10 * c + d) = 2243 := by 
  have h5 : a < 10 := h₀ 
  have h6 : b < 10 := h₁
  have h7 : c < 10 := h₂
  have h8 : d < 10 := h₃
  interval_cases a <;> interval_cases b <;> omega