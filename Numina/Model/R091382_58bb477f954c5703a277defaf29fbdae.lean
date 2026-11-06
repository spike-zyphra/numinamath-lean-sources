import Mathlib

theorem algebra_9854 (a b c : ℝ)
    (h₀ : a^2 - b * c - 8 * a + 7 = 0)
    (h₁ : b^2 + c^2 + b * c - 6 * a + 6 = 0) :
    1 ≤ a ∧ a ≤ 9 := by

  have hbc : b * c = a^2 - 8 * a + 7 := by
    nlinarith
  
  have heq : b^2 + c^2 = 14 * a - 13 - a^2 := by
    have h2 : b^2 + c^2 = 14 * a - 13 - a^2 := by
      nlinarith [h₀, h₁]
    linarith

  have h2 : b^2 + c^2 ≥ 2 * (b * c) := by
    nlinarith [sq_nonneg (b - c)]

  rw [show b * c = a^2 - 8 * a + 7 by linarith [h₀]] at h2
  rw [show b^2 + c^2 = 14 * a - 13 - a^2 by linarith [heq]] at h2

  have h3 : (a - 1) * (a - 9) ≤ 0 := by nlinarith

  constructor
  · nlinarith
  · nlinarith