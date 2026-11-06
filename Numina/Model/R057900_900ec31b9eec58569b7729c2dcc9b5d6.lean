import Mathlib

theorem algebra_268669 (a c : ℝ) (h₁ : -4 ≤ a * 1^2 - c ∧ a * 1^2 - c ≤ -1)
    (h₂ : -1 ≤ a * 2^2 - c ∧ a * 2^2 - c ≤ 5) :
    -1 ≤ a * 3^2 - c ∧ a * 3^2 - c ≤ 20 := by
  constructor
  · -- Proof that -1 ≤ a * 3^2 - c
    linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · -- Proof that a * 3^2 - c ≤ 20
    linarith [h₁.1, h₁.2, h₂.1, h₂.2]