import Mathlib

open Real

theorem calculus_166012 (k : ℝ) (C : ℝ) :
    ∀ x, deriv (fun x => k * (x - 1) + C * exp (-x)) x + (k * (x - 1) + C * exp (-x)) - k * x = 0 := by
  intro x
  simp [deriv_add, deriv_mul, deriv_id'', mul_comm C, differentiableAt_exp, differentiableAt_id', mul_comm k]
  all_goals
    field_simp [exp_neg]
    <;> ring