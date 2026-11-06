import Mathlib

theorem algebra_197538
    (x y z : ℝ)
    (h₀ : 0 < x)
    (h₁ : 0 < y)
    (h₂ : 0 < z)
    (h₃ : x^2 + x * y + y^2 = 27)
    (h₄ : y^2 + y * z + z^2 = 16)
    (h₅ : z^2 + x * z + x^2 = 43) :
    x * y + y * z + x * z = 24 := by
  nlinarith [mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₂ h₀, 
            h₃, h₄, h₅]