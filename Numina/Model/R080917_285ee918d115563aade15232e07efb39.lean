import Mathlib

theorem algebra_3424
  (a b c : ℝ)
  (h₀ : a + b + c = 0)
  (h₁ : a * b * c = 17) :
  a^3 + b^3 + c^3 = 51 := by
  have h2 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + a * c + b * c)) := by
    ring
  rw [h₀] at h2
  have h3 : a^3 + b^3 + c^3 - 3 * (a * b * c) = 0 := by 
    linarith
  have h4 : a^3 + b^3 + c^3 = 3 * (a * b * c) := by
    linarith
  rw [h₁] at h4
  linarith