import Mathlib

open Real

theorem calculus_143158 {y : ℝ → ℝ} (hy : y = fun x => x * exp (-x^2 / 2)) :
    ∀ x, x * deriv y x = (1 - x^2) * y x := by
  intro x
  rw [hy]
  simp [deriv_mul, deriv_id'', differentiableAt_exp, differentiableAt_id', mul_comm]
  <;> field_simp [exp_neg, mul_comm]
  <;> ring_nf
  <;> field_simp [exp_neg, mul_comm]
  <;> ring_nf