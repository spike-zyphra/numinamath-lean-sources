import Mathlib

theorem algebra_137371 (f : ℝ → ℝ) (hf : f = fun x => (1/2)*x^2 + 2*x - 1) :
    ∀ x, f x = (1/2)*(x + 2)^2 - 3 := by
  intro x
  rw [hf]
  ring