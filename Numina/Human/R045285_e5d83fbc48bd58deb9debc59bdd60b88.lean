import Mathlib

theorem algebra_14626 (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : a + b = 260) (h₂ : b + c = 245) (h₃ : c + d = 270) :
    a + d = 285 := by 
  linarith