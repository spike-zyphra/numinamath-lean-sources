import Mathlib

theorem algebra_252826 {k : ℝ} (hk : k ≠ 0 ∧ k ≠ 1) :
    ∃ f : ℝ → ℝ, ∀ x, f x = -k / abs k * x := by
  use fun x => -k / abs k * x
  intro x
  rfl