import Mathlib

theorem algebra_5205 (f : ℝ → ℝ) (hf : f = fun x => x ^ 3 - 37 * x + 84) :
    f = fun x => (x + 7) * (x - 3) * (x - 4) := by 
  funext x
  rw [hf]
  ring