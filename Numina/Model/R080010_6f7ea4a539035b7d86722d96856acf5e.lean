import Mathlib

open Real

theorem calculus_99536 {y : ℝ → ℝ} (hy : y = fun x => exp (2 * x) * cos x) :
    deriv y = fun x => exp (2 * x) * (2 * cos x - sin x) := by
  rw [hy]
  funext x
  simp [deriv_mul, differentiableAt_exp, differentiableAt_cos, mul_comm, mul_assoc]
  <;> field_simp [exp_ne_zero]
  <;> ring_nf <;> field_simp [exp_ne_zero]
  <;> ring