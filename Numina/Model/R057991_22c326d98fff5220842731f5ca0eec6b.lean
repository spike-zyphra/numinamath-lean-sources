import Mathlib

theorem algebra_4475 {f : ℝ → ℝ} :
    ∀ x, f (2 - x) = f (-(x - 2)) := by
  intro x
  have h : (2 - x : ℝ) = -(x - 2) := by
    ring
  rw [h]
  all_goals ring