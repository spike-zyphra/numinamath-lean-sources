import Mathlib

open Real

theorem calculus_155346 {f : ℝ → ℝ} (hf : f = fun x => (x ^ 2 + 2) * (2 * x + 1)) :
    deriv f = fun x => 6 * x ^ 2 + 2 * x + 4 := by
  rw [hf]
  funext x
  simp [deriv_mul, deriv_add, deriv_pow, deriv_const, deriv_id'', mul_comm]
  all_goals
    ring_nf <;> norm_num <;> ring
  all_goals
    ring_nf <;> norm_num <;> ring
  all_goals
    ring_nf <;> norm_num <;> ring