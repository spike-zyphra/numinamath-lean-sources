import Mathlib

theorem algebra_20997 {a b c : ℝ} (h₀ : a < c) (h₁ : b < 0) :
    a + b < c + b ∧ a - b < c - b := by
  constructor
  · -- Prove a + b < c + b using the given h₀: a < c
    linarith
  · -- Prove a - b < c - b using the given h₀: a < c
    linarith