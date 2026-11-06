import Mathlib

theorem algebra_5571 {f : Polynomial ℝ} (hf : f = X^3 - 12*X^2 + 41*X - 42) :
    f = (X-2)*(X-3)*(X-7) := by 
  rw [hf]
  ring