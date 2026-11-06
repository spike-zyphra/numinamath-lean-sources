import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_148506 {y : ℝ → ℝ} (hy : y = λ x => (x^2 + 1)^(cos x)) :
    deriv y = λ x => (x^2 + 1)^(cos x) * ((2 * x * cos x / (x^2 + 1)) - (sin x * log (x^2 + 1))) := by
  rw [hy]
  funext x
  simp [deriv_pow, deriv_mul, deriv_id'', mul_comm]
  all_goals
    field_simp [Real.rpow_def_of_pos, add_pos, show 0 < (x ^ 2 + 1: ℝ) by positivity, Real.log_pos]
    <;> ring_nf
    <;> field_simp [Real.rpow_def_of_pos, add_pos, show 0 < (x ^ 2 + 1: ℝ) by positivity, Real.log_pos]
    <;> ring