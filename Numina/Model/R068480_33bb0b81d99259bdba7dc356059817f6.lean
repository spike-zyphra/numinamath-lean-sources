import Mathlib

theorem algebra_312687 {k : ℝ} (hk : k ≠ 0) :
    ∃ f : ℝ → ℝ, ∀ x, f x = -k / abs k * x := by 
  use λ x => -k / abs k * x
  all_goals simp