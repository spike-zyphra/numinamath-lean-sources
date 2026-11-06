import Mathlib

theorem algebra_239091 (a b c d : ℕ) (h₀ : a * c + a * d + b * c + d * b = 68) (h₁ : c + d = 4) :
    a + b + c + d = 21 := by
  -- The expression a*c + a*d + b*c + b*d can be rearranged to (a+b)(c+d)
  have h2 : a * c + a * d + b * c + d * b = (a + b) * (c + d) := by
    ring
  rw [h2] at h₀
  rw [show c + d = 4 by linarith] at h₀
  have h4 : a + b = 17 := by
    omega
  calc
    a + b + c + d = (a + b) + (c + d) := by
      ring
    _ = 17 + 4 := by
      rw [h4, h₁]
    _ = 21 := by
      norm_num