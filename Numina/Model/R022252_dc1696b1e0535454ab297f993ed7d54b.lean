import Mathlib

open Real

theorem calculus_140159 (f : ℝ → ℝ) (hf : f = fun x => exp x * (cos (2 * x) + 2 * sin (2 * x))) :
    deriv f = fun x => 5 * exp x * cos (2 * x) := by 
  rw [hf]
  funext x
  simp [deriv_mul, deriv_add, deriv_sub, deriv_mul, deriv_id'', mul_comm]
  field_simp [exp_ne_zero x]
  ring_nf
  <;> simp [sin_sq, cos_sq]
  <;> ring