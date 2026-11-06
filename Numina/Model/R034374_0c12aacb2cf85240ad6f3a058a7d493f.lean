import Mathlib

theorem algebra_275743 {f : ℝ → ℝ} (hf : ∀ x, f (x + 1) - f x = 1)
    (F : ℝ → ℝ) (hF : F = fun x => f x - x) :
    ∃ c, Function.Periodic F c := by
  use 0
  unfold Function.Periodic
  intro x
  simp [hF]