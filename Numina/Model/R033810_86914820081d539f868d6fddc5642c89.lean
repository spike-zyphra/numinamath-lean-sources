import Mathlib

theorem algebra_9144 {f : ℝ → ℝ} (hf : f = fun x => (2 * Real.pi * x) ^ 2) : deriv f = fun x => 8 * Real.pi ^ 2 * x := by
  rw [hf]
  funext x
  simp [deriv_pow, deriv_mul, deriv_id'', mul_comm]
  <;> ring