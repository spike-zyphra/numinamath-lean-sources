import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_140858 {r : ℝ → ℝ}
  (hr : r = λ t => log (exp t / (exp t + 1))) :
  deriv r 0 = 1 / 2 := by
  rw [hr]
  -- Use derivative rules for logarithm of a function
  -- The derivative of log(g(t)) is g'(t)/g(t)
  simp [deriv_log, deriv_div, deriv_id'', exp_ne_zero, add_ne_zero, differentiableAt_exp]
  all_goals
    norm_num [exp_zero]
    <;> field_simp [exp_ne_zero] <;> ring
    <;> norm_num [exp_zero]
    all_goals norm_num [exp_zero]
    <;> field_simp [exp_ne_zero] <;> ring
    all_goals norm_num [exp_zero]