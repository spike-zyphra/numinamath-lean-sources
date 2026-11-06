import Mathlib

theorem algebra_284734 (a b c d : ℚ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : a + b + c + d = 280) (h₂ : b = a - 16) (h₃ : c = a + b - 24)
    (h₄ : d = a + c) :
    a = 53 + 5 / 7 ∧ b = 37 + 5 / 7 ∧ c = 67 + 3 / 7 ∧ d = 121 + 1 / 7 := by
  constructor
  · -- Solving for a
    linarith [h₁, h₂, h₃, h₄]
  constructor
  · -- Solving for b
    linarith [h₂, h₁, h₃, h₄]
  constructor
  · -- Solving for c
    linarith [h₃, h₂, h₁, h₄]
  · -- Solving for d
    linarith [h₄, h₂, h₃, h₁]