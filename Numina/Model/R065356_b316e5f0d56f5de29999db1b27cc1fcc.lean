import Mathlib

theorem algebra_9565 (f : Polynomial ℤ) (hf : f = X ^ 8 + X ^ 4 + 1) :
    f = (X ^ 2 + X + 1) * (X ^ 2 - X + 1) * (X ^ 4 - X ^ 2 + 1) := by 
  rw [hf]
  ring