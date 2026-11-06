import Mathlib

theorem algebra_245643 {x y : ℝ} (h₀ : x + y = 10) (h₁ : x^3 + y^3 = 400) :
    x^2 + y^2 = 60 := by
  have h2 : x^3 + y^3 = (x + y)^3 - 3 * (x * y) * (x + y) := by
    ring
  have h3 : x * y = 20 := by
    rw [h2, h₀] at h₁
    nlinarith
  have h4 : x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by
    ring
  rw [h₀, h3] at h4
  nlinarith