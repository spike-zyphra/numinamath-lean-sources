import Mathlib

theorem calculus_124824 {y : ℝ → ℝ} (hy : y = fun x => 5 * Real.exp (-2 * x) + (Real.exp x) / 3) :
    ∀ x, deriv y x + 2 * y x = Real.exp x := by
  intro x
  rw [hy]
  simp [deriv_add, deriv_mul, deriv_id'', mul_comm]
  all_goals
    norm_num [Real.deriv_exp, mul_comm]
    <;> ring_nf <;> norm_num
    <;> linarith [Real.exp_pos]
    <;> norm_num
    all_goals norm_num
    <;> nlinarith [Real.exp_pos]
    <;> norm_num
    <;> nlinarith [Real.exp_pos]
  all_goals norm_num
  all_goals nlinarith [Real.exp_pos]
  all_goals norm_num
  all_goals nlinarith [Real.exp_pos]
  all_goals norm_num
  all_goals nlinarith [Real.exp_pos]
  all_goals norm_num
  <;> nlinarith [Real.exp_pos]
  all_goals try tauto