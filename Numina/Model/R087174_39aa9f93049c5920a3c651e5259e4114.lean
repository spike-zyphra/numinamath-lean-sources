import Mathlib

theorem algebra_203835 (a b y : ℝ) (h₀ : a + b + y = 5) (h₁ : a * b + b * y + a * y = 3) :
    y ≤ 13 / 3 := by
  have h2 : a + b = 5 - y := by linarith
  have h3 : a * b = 3 - 5 * y + y^2 := by
    have : a * b + y * (a + b) = 3 := by
      linarith [h₀, h₁]
    rw [h2] at this
    linarith
  have h4 : (a + b) ^ 2 - 4 * (a * b) ≥ 0 := by
    nlinarith [sq_nonneg (a - b)]
  rw [h2, h3] at h4
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - (5 - y)), sq_nonneg (y - 13/3), sq_nonneg (y + 1)]