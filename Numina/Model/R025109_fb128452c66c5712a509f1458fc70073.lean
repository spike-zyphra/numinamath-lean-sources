import Mathlib

theorem algebra_140767 (y : ℝ → ℝ) (hy : y = fun x => 10^(2*x - 3)) :
    deriv y = fun x => 2 * y x * Real.log 10 := by
  rw [hy]
  funext x
  simp [deriv_pow, deriv_const, deriv_id', mul_comm]
  all_goals
    field_simp [Real.rpow_def_of_pos]
    <;> ring_nf
    <;> field_simp [Real.rpow_def_of_pos]
    <;> ring