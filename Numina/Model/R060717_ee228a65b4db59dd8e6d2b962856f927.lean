import Mathlib

theorem algebra_603262
    (x y z : ℝ)
    (h₀ : 0 < x)
    (h₁ : 0 < y)
    (h₂ : 0 < z)
    (h₃ : x^2 + x * y + y^2 / 3 = 25)
    (h₄ : y^2 / 3 + z^2 = 9)
    (h₅ : x^2 + x * y + z^2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  nlinarith [mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₂ h₀]