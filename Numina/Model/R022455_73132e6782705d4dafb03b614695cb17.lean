import Mathlib

open Real

theorem calculus_145401 (f : ℝ → ℝ) (hf : f = fun x => 2 * exp (-1/2 * x)) :
    deriv f = fun x => -exp (-1/2 * x) := by 
  funext x 
  rw [hf]
  simp [deriv_const_mul, deriv_mul, deriv_id'', mul_comm]
  all_goals ring_nf 
  <;> field_simp [exp_ne_zero, mul_add, add_mul]
  <;> ring