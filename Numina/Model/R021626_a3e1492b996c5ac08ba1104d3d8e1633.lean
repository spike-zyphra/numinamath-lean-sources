import Mathlib

theorem algebra_10991 {f : ℝ → ℝ} (hf : f = fun x => x^3 + 2*x^2 + 3*x + 4) :
    ∃ x y, ∀ t, f t = -f (-t + x) + y := by
  use (-4 / 3)
  use (140 / 27)
  intro t
  simp [hf]
  ring