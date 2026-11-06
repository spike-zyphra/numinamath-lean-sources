import Mathlib

theorem algebra_47500 (a b c x y : ℝ) (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : c ≠ a)
    (h₃ : a^3 + a * x + y = 0) (h₄ : b^3 + b * x + y = 0) (h₅ : c^3 + c * x + y = 0) :
    a + b + c = 0 := by 
  have h1 : a^2 + a * b + b^2 + x = 0 := by
    have : (a - b) * (a^2 + a * b + b^2 + x) = 0 := by 
      linarith [h₃, h₄]
    cases' (mul_eq_zero.mp this) with hab h
    · -- a - b = 0, which contradicts a ≠ b
      exfalso
      exact h₀ (by linarith)
    · -- a^2 + a * b + b^2 + x = 0
      linarith
  have h2 : b^2 + b * c + c^2 + x = 0 := by
    have : (b - c) * (b^2 + b * c + c^2 + x) = 0 := by 
      linarith [h₄, h₅]
    cases' (mul_eq_zero.mp this) with hbc h
    · -- b - c = 0, which contradicts b ≠ c
      exfalso
      exact h₁ (by linarith)
    · -- b^2 + b * c + c^2 + x = 0
      linarith
  have h3 : c^2 + c * a + a^2 + x = 0 := by
    have : (c - a) * (c^2 + c * a + a^2 + x) = 0 := by 
      linarith [h₅, h₃]
    cases' (mul_eq_zero.mp this) with hca h
    · -- c - a = 0, which contradicts c ≠ a
      exfalso
      exact h₂ (by linarith)
    · -- c^2 + c * a + a^2 + x = 0
      linarith
  have : (c - a) * (a + b + c) = 0 := by
    linarith [h1, h2]
  cases' (mul_eq_zero.mp this) with hca h
  · -- c - a = 0, which contradicts c ≠ a
    exfalso
    exact h₂ (by linarith)
  · -- a + b + c = 0
    linarith