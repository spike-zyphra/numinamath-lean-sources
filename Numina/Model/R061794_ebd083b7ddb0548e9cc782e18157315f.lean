import Mathlib

theorem algebra_5614 {f : Polynomial ℤ} (hf : f = X ^ 2 + 14 * X + 45) : f = (X + 9) * (X + 5) := by 
  rw [hf]
  ring_nf