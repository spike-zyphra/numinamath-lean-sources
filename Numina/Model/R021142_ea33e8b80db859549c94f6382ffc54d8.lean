import Mathlib

theorem algebra_315759 {a b c : ℝ} (h₀ : a^2 + b * c = 14) (h₁ : b^2 - 2 * b * c = -6) :
    3 * a^2 + 4 * b^2 - 5 * b * c = 18 := by
  have h2 : a^2 = 14 - b * c := by linarith
  have h3 : b^2 = -6 + 2 * b * c := by linarith
  rw [h2, h3]
  ring