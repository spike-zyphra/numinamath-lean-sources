import Mathlib

open Real Set

theorem inequalities_106332 (a b c d x y z t : ℝ)
    (h₀ : 0 ≤ a ∧ a ≤ 1) (h₁ : 0 ≤ b ∧ b ≤ 1) (h₂ : 0 ≤ c ∧ c ≤ 1) (h₃ : 0 ≤ d ∧ d ≤ 1)
    (h₄ : 1 ≤ x) (h₅ : 1 ≤ y) (h₆ : 1 ≤ z) (h₇ : 1 ≤ t)
    (h₈ : a + b + c + d + x + y + z + t = 8) :
    a^2 + b^2 + c^2 + d^2 + x^2 + y^2 + z^2 + t^2 ≤ 28 := by
  have h1 : a ^ 2 ≤ a := by
    have h1 : 0 ≤ a := h₀.1
    have h2 : a ≤ 1 := h₀.2
    nlinarith
  have h2 : b ^ 2 ≤ b := by
    have h1 : 0 ≤ b := h₁.1
    have h2 : b ≤ 1 := h₁.2
    nlinarith
  have h3 : c ^ 2 ≤ c := by
    have h1 : 0 ≤ c := h₂.1
    have h2 : c ≤ 1 := h₂.2
    nlinarith
  have h4 : d ^ 2 ≤ d := by
    have h1 : 0 ≤ d := h₃.1
    have h2 : d ≤ 1 := h₃.2
    nlinarith
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (t - 1),
    h₄, h₅, h₆, h₇, 
    h₀.1, h₁.1, h₂.1, h₃.1, 
    h₀.2, h₁.2, h₂.2, h₃.2
  ]