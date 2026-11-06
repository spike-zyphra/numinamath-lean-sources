import Mathlib

theorem algebra_108863 (a b c d : ℝ) (h₀ : a + b + c + d = 2014)
    (h₁ : d = a + 16) (h₂ : d = b - 16) (h₃ : d = c / 16) :
    a = 90 ∧ b = 122 ∧ c = 1696 ∧ d = 106 := by
  refine' ⟨_, _, _, _⟩ <;>
  linarith