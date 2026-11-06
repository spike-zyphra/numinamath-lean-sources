import Mathlib

open Real

theorem calculus_131744 {y : ℝ → ℝ} (hy : y = fun x => exp (x^2) / (1 + x^2)) :
    deriv y = fun x => 2 * x^3 * exp (x^2) / (1 + x^2)^2 := by
  rw [hy]
  funext x
  simp [deriv_div, deriv_mul, deriv_pow, deriv_id'', mul_comm, differentiableAt_exp, differentiableAt_pow, add_assoc, mul_assoc]
  all_goals
    field_simp [(show (1 + x ^ 2 : ℝ) ≠ 0 by positivity)]
    <;> ring_nf
    <;> norm_num