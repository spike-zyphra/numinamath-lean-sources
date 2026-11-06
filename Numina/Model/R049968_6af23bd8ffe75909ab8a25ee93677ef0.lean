import Mathlib

open Real

theorem calculus_162021 (a : ℝ) (ha : a > 0) :
    deriv (fun x => a ^ (x ^ 2)) = fun x => 2 * log a * x * a ^ (x ^ 2) := by
  funext x
  simp [deriv_pow, deriv_id'', mul_comm]
  <;> ring_nf <;> field_simp [Real.rpow_def_of_pos ha] <;> ring
  all_goals
    linarith