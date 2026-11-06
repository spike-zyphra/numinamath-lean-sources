import Mathlib

theorem algebra_159399 (s s' : ℝ → ℝ) (h₀ : s = fun t => 6 * t) (h₁ : s' = fun t => 0.5 * t ^ 2 + 25):
    ∀t > 0, s' t - s t > 0 := by
  intro t ht
  have eq1 : s' t = 0.5 * t^2 + 25 := by
    simp [h₁]
  have eq2 : s t = 6 * t := by
    simp [h₀]
  calc
    s' t - s t = (0.5 * t^2 + 25) - (6 * t) := by
      rw [eq1, eq2]
    _ = 0.5 * t^2 - 6 * t + 25 := by ring
    _ > 0 := by
      have h2 : 0.5 * t^2 - 6 * t + 25 > 0 := by
        nlinarith [sq_nonneg (t - 6)]
      linarith