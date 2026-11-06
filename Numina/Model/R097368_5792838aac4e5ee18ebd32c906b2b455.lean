import Mathlib

theorem algebra_229065 {a : ℕ → ℝ} (x₀ : ℝ)
    (h₁ : x₀^4 + a 1 * x₀^3 + a 2 * x₀^2 + a 3 * x₀ + a 4 = 0)
    (h₂ : 4 * x₀^3 + 3 * a 1 * x₀^2 + 2 * a 2 * x₀ + a 3 = 0) :
    (X - x₀)^2 ∣ X^4 + a 1 * X^3 + a 2 * X^2 + a 3 * X + a 4 := by
  use (X^2 + (a 1 + 2 * x₀) * X + (a 2 + 2 * a 1 * x₀ + 3 * x₀^2))
  have h₃ : a 4 = - (x₀^4 + a 1 * x₀^3 + a 2 * x₀^2 + a 3 * x₀) := by linarith
  have h₄ : a 3 = - (4 * x₀^3 + 3 * a 1 * x₀^2 + 2 * a 2 * x₀) := by linarith
  rw [h₃, h₄]
  ring_nf
  <;> nlinarith [sq_nonneg (x₀ ^ 2), sq_nonneg (a 1 * x₀), sq_nonneg (a 2 * x₀), sq_nonneg (x₀), sq_nonneg (X - x₀)]