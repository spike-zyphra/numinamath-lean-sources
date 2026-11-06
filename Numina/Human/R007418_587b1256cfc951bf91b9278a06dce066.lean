import Mathlib

theorem algebra_159399 (s s' : ℝ → ℝ) (h₀ : s = fun t => 6 * t) (h₁ : s' = fun t => 0.5 * t ^ 2 + 25):
    ∀t > 0, s' t - s t > 0 := by
  rw [h₀, h₁]
  simp
  intro t ht
  nlinarith [sq_nonneg (t - 6)]