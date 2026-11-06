import Mathlib

theorem algebra_5752 (f : ℝ → ℝ) (hf : f = fun x => 5*x^3+38*x^2+19*x-14) :
    f = fun x => (x+1)*(5*x-2)*(x+7) := by 
  funext x
  rw [hf]
  ring