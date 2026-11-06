import Mathlib

theorem algebra_601355 (a b c d e f : ℝ)
    (h₀ : a = (b + c + d) / 3) (h₁ : b = (a + c + e) / 3)
    (h₂ : c = (a + b + f) / 3) (h₃ : d = (a + e + f) / 3)
    (h₄ : e = (b + d + f) / 3) (h₅ : f = (c + d + e) / 3) :
    a = b ∧ b = c ∧ c = d ∧ d = e ∧ e = f := by
  constructor
  · -- Let's try to prove a = b first
    nlinarith [h₀, h₁, h₂, h₃, h₄, h₅]
  constructor
  · -- b = c
    nlinarith [h₀, h₁, h₂, h₃, h₄, h₅]
  constructor
  · -- c = d
    nlinarith [h₀, h₁, h₂, h₃, h₄, h₅]
  constructor
  · -- d = e
    nlinarith [h₀, h₁, h₂, h₃, h₄, h₅]
  · -- e = f
    nlinarith [h₀, h₁, h₂, h₃, h₄, h₅]