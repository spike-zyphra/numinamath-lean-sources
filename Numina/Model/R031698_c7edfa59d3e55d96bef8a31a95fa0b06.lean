import Mathlib

theorem calculus_161965 (y : ℝ → ℝ) (hy : y = fun x => Real.sin (5 * x)) :
    deriv y = fun x => 5 * Real.cos (5 * x) := by 
  rw [hy]
  funext x 
  simp [deriv_const_mul, deriv_id', mul_comm]
  all_goals ring