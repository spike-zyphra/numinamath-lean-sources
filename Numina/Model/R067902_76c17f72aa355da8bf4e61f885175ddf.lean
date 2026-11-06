import Mathlib

theorem algebra_270839 (a j r : ℝ) (h₀ : 0 < a ∧ 0 < j ∧ 0 < r)
    (h₁ : a + j = 101) (h₂ : a + r = 91) (h₃ : r + j = 88) :
    a = 52 := by 
  linarith