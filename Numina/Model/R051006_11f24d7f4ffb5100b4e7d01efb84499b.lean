import Mathlib

theorem algebra_14525 (f : ℝ → ℝ) (hf : f = fun x => 2 - 4 * x - 6 * x ^ 2 + 8 + 10 * x - 12 * x ^ 2 - 14 + 16 * x + 18 * x ^ 2) :
    f = fun x => 22 * x - 4 := by
  funext x
  rw [hf]
  ring