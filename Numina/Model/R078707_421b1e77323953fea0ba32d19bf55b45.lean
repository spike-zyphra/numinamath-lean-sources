import Mathlib

theorem algebra_5534 (f : Polynomial ℤ) (hf : f = X ^ 3 + 10 * X ^ 2 + 31 * X + 30) :
    f = (X + 2) * (X + 3) * (X + 5) := by 
  rw [hf]
  ring