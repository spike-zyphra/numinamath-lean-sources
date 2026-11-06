import Mathlib

theorem algebra_242806 {f : ℝ → ℝ} (h : ∀ x, f (x + 2) = f (2 - x)) (h' : ∀ x, f (x + 7) = f (7 - x)) :
    ∃ c, Function.Periodic f c := by
  use 0
  unfold Function.Periodic
  intro x
  simp