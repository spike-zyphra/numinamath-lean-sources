import Mathlib

theorem algebra_10221 {f : Polynomial ℝ} (hf : f = 58 * X ^ 5 - 203 * X ^ 11) :
    f = -29 * X ^ 5 * (7 * X ^ 6 - 2) := by 
  rw [hf]
  ring_nf