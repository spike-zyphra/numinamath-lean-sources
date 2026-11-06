import Mathlib

theorem algebra_4365 (a d : ℤ) (h₀ : 0 < a) (h₁ : 0 < d)
    (h₂ : a + d = 20) (h₃ : a + 2 * d = 30) :
    a + 3 * d = 40 ∨ a + 3 * d = 50 ∨ a + 3 * d = 60 := by
  have h4 : d = 10 := by linarith
  have h5 : a = 10 := by linarith [h₂, h4]
  left
  linarith [h5, h4]