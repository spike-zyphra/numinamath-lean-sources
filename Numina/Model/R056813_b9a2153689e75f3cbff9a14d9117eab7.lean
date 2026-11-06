import Mathlib

theorem algebra_6698 {f : Polynomial ℤ} (hf : f = -X^2 + 2*X + 48) :
    f = (8 - X)*(X + 6) := by 
  rw [hf]
  ring