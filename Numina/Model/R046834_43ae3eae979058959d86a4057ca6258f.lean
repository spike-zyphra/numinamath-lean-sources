import Mathlib

theorem algebra_233213 {x y : ℝ} (h₀ : x^2 + y^2 = 2) (h₁ : (x^3 + y^3)^2 = 8) :
    x^4 + y^4 = 4 := by
  have h2 : x^4 + y^4 = (x^2 + y^2)^2 - 2 * (x * y) ^ 2 := by
    nlinarith
  rw [h₀] at h2
  have h3 : x^3 + y^3 = (x + y) * (x^2 - x * y + y^2) := by
    ring
  have h4 : x^2 - x * y + y^2 = 2 - x * y := by
    have h5 : x^2 + y^2 = 2 := h₀
    nlinarith
  have h6 : x^3 + y^3 = (x + y) * (2 - x * y) := by
    rw [h3, h4]
  have h7 : (x^3 + y^3)^2 = (x + y) ^ 2 * (2 - x * y) ^ 2 := by
    rw [h6]
    all_goals ring
  have h8 : (x + y) ^ 2 = 2 + 2 * (x * y) := by
    nlinarith [h₀]
  rw [h8] at h7
  rw [h7] at h₁
  have h8 : (x * y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x * y - 3), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y), h₀]
  have h9 : x * y = 0 := by
    nlinarith
  rw [h9] at h2
  nlinarith