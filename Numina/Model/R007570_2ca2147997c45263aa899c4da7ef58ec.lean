import Mathlib

theorem algebra_113064 {f : ℝ → ℝ} (c : ℝ)
    (h0 : ∀ x, 1 + f x ≠ 0)
    (h : ∀ x, f (x + c) = 2 / (1 + f x) - 1) :
    ∃ c, Function.Periodic f c := by 
  use 0 
  unfold Function.Periodic 
  intro x
  simp