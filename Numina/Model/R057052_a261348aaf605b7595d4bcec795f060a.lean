import Mathlib

open Real

theorem calculus_155555 (f : ℝ → ℝ) (hf : f = fun x => exp (x ^ 2)) :
    deriv f = fun x => 2 * x * exp (x ^ 2) := by
  rw [hf]
  funext x
  simp [deriv_pow, differentiableAt_exp, deriv_id'', mul_comm]
  all_goals ring_nf <;> field_simp
  all_goals try linarith