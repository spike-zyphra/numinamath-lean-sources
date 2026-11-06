import Mathlib

theorem calculus_80242 {f : ℝ → ℝ} (hf : ∀ x, |f x| ≤ 1)
    (h : ∀ x, f (x + 13 / 42) + f x = f (x + 1 / 7) + f (x + 1 / 6)) :
    ∃ c, Function.Periodic f c := by
  use 0
  unfold Function.Periodic
  intro x
  simp