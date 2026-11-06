import Mathlib

open Real

theorem calculus_131134 {f : ℝ → ℝ}
    (hf : f = fun x => exp x / 2 * ((x ^ 2 - 1) * cos x + (x - 1) ^ 2 * sin x)) :
    deriv f = fun x => x ^ 2 * exp x * cos x := by 
  rw [hf]
  funext x
  simp [deriv_mul, deriv_add, deriv_mul, deriv_id'', mul_comm, mul_assoc]
  field_simp [exp_ne_zero x]
  ring_nf
  <;> field_simp [exp_ne_zero x]
  <;> ring