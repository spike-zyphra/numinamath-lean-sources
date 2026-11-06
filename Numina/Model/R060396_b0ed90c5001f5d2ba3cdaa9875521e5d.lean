import Mathlib

theorem algebra_134116 (a b c d e f : ℝ)
    (h₀ : a = (b + c + d) / 3) (h₁ : b = (a + c + e) / 3)
    (h₂ : c = (a + b + f) / 3) (h₃ : d = (e + f + a) / 3)
    (h₄ : e = (b + d + f) / 3) (h₅ : f = (c + e + d) / 3) :
    a = b ∧ b = c ∧ c = d ∧ d = e ∧ e = f := by

  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith