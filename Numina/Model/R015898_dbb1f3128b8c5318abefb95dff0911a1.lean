import Mathlib

open Real

theorem calculus_136490 {f : ℝ → ℝ} (hf : f = fun x => (exp (2 * x) * (2 - sin (2 * x) - cos (2 * x)) / 8)) :
    deriv f = fun x => exp (2 * x) * sin x ^ 2 := by
  rw [hf]
  funext x
  simp [deriv_div_const, deriv_mul, deriv_id'', mul_comm]
  field_simp [exp_ne_zero (2 * x)]
  ring_nf
  <;> simp [exp_ne_zero (2 * x), sin_sq, cos_sq]
  <;> ring
  <;> try norm_num
  <;> try ring_nf <;> try simp [exp_ne_zero (2 * x), sin_sq, cos_sq]
  <;> try ring_nf
  <;> try nlinarith [Real.exp_pos (2 * x), sq_nonneg (sin x), sq_nonneg (cos x - 1)]
  <;> try tauto