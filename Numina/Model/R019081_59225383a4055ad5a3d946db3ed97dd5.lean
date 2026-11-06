import Mathlib

theorem algebra_140853 {a b c : ℝ}
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a = b)
    (h₂ : b = c)
    (h₃ : b = a + 3)
    (h₄ : c = b + 3)
    (h₅ : b * a = c * b - 12)
    (h₆ : c * b = a * c - 24) :
    a * b = 20 := by
  have h7 : a = b := by linarith [h₁]
  have h8 : b = a + 3 := by linarith [h₃]
  have h9 : (a : ℝ) = a + 3 := by
    have h10 : b = a := by linarith [h7]
    linarith [h10, h₃]
  linarith