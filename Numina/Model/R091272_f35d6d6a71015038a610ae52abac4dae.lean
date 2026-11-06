import Mathlib

theorem algebra_111963 (a b c d : ℤ) (h₀ : a + b + c + d = 2021)
    (h₁ : a * b + c * d + a * d + b * c = x) :
    (a + 1) * (b + 1) + (c + 1) * (d + 1) + (a + 1) * (d + 1) + (b + 1) * (c + 1) = x + 4046 := by
  have h₂ : (a + 1) * (b + 1) + (c + 1) * (d + 1) + (a + 1) * (d + 1) + (b + 1) * (c + 1) =
      a * b + c * d + a * d + b * c + 2 * (a + b + c + d) + 4 := by
    ring
  rw [h₂, h₀]
  linarith [h₁]