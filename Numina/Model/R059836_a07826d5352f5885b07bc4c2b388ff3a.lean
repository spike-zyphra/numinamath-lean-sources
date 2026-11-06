import Mathlib

theorem algebra_6358 {x y : ℝ} (h₀ : x + y = 2) (h₁ : x^3 + y^3 = 3) :
    x^2 + y^2 = 7 / 3 := by
  have h2 : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by 
    ring
  rw [h₀] at h2
  have h3 : x^3 + y^3 = 8 - 6 * (x * y) := by
    nlinarith
  rw [h₁] at h3
  have h4 : x * y = 5 / 6 := by
    nlinarith
  have h5 : x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by
    ring
  rw [h₀, h4] at h5
  nlinarith