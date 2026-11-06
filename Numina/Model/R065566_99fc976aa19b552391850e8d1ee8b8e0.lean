import Mathlib

theorem inequalities_290774 {a b c d : ℝ} (h₀ : a^2 < 4 * b) (h₁ : c^2 < 4 * d) :
    ((a + c) / 2)^2 < 4 * ((b + d) / 2) := by 
  nlinarith [sq_nonneg (a - c), sq_nonneg (a + c), h₀, h₁]