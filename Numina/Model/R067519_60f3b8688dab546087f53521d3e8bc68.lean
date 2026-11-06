import Mathlib

theorem algebra_116487 {x y : ℝ} (h₀ : x^2 - y^2 = 6) (h₁ : (x - 2)^2 - (y - 2)^2 = 18) :
    x + y = -2 := by
  have h2 : (x - y) * (x + y) = 6 := by
    nlinarith
  have h3 : (x - y) * (x + y - 4) = 18 := by
    nlinarith
  have h4 : (x - y) = -3 := by
    nlinarith
  have h5 : x + y = -2 := by
    rw [h4] at h2
    linarith
  exact h5