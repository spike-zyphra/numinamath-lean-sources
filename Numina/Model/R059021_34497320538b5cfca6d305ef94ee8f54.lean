import Mathlib

theorem algebra_11152
    (a b c : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : 2 * (a + b) = a * b)
    (h₄ : a + b + c = a * b * c) :
    c ≤ 8 / 15 := by

  nlinarith [sq_nonneg (a - b), sq_nonneg (a - 4), sq_nonneg (b - 4),
          mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂
      ]