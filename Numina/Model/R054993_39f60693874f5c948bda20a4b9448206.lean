import Mathlib

theorem algebra_7419 (f : Polynomial ℝ) (hf : f = (X^2 + X + 2)^3 - 8) :
    f = X * (X + 1) * (X^2 + 3) * (X^2 + 2 * X + 4) := by
  rw [hf]
  ring_nf
  <;> simp [pow_three]
  <;> ring