import Mathlib

theorem algebra_214246 {f : ℝ → ℝ} (h : ∀ x, f (x + 1) + f (x - 1) = √2 * f x) :
    ∃ c, Function.Periodic f c := by 
  use 0
  unfold Function.Periodic
  intro x
  simp