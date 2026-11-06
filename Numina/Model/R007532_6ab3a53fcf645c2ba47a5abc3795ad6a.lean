import Mathlib

theorem algebra_20715 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 - 3 * x + 4) :
    ∀ x, f (2 * x) = 4 * x ^ 2 - 6 * x + 4 := by
  intro x 
  calc 
    f (2 * x) = (2 * x) ^ 2 - 3 * (2 * x) + 4 := by 
      rw [hf]
    _ = 4 * x ^ 2 - 6 * x + 4 := by 
      ring