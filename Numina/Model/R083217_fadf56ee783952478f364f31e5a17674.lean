import Mathlib

theorem algebra_13587 (f : Polynomial ℤ) (hf : f = X ^ 4 + X ^ 3 - 13 * X ^ 2 - X + 12) :
    f = (X - 1) * (X + 1) * (X - 3) * (X + 4) := by 
  rw [hf]
  ring_nf