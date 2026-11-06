import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155547 (f : ℝ → ℝ) (hf : f = λ x => 0.5^(sin (4 * x))) :
    deriv f = λ x => 4 * cos (4 * x) * 0.5^(sin (4 * x)) * log 0.5 := by 
  rw [hf]
  funext x
  simp [Real.rpow_def_of_pos, deriv_mul, deriv_id'', deriv_add, deriv_sub, deriv_const,
    Real.log_rpow, mul_comm]
  all_goals field_simp [Real.rpow_def_of_pos]
  <;> ring_nf