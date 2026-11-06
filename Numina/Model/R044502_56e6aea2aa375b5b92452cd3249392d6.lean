import Mathlib

theorem algebra_8989 {f : ℝ → ℝ} (hf : f = fun x => 2 * x * Real.sin (2 * x + 5)) :
  deriv f = fun x => 2 * Real.sin (2 * x + 5) + 4 * x * Real.cos (2 * x + 5) := by 
  rw [hf]
  funext x 
  simp [deriv_mul, deriv_id'', mul_comm]
  all_goals
    field_simp [Real.deriv_sin]
    ring