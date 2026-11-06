import Mathlib

theorem algebra_2165 {a b c d : ℝ} (h₀ : a + b = c + d) (h₁ : a + d < b + c)
    (h₂ : c < d) : a < c ∧ c < d ∧ d < b := by
  constructor
  · -- Derive a < c
    nlinarith
  constructor
  · -- c < d is given
    linarith
  · -- Derive d < b
    nlinarith [h₀, h₁, h₂]