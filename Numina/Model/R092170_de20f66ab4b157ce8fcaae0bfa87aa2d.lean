import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_147791 {f : ℝ → ℝ} (hf : ∀ x, f x = 2 * (x - 1) - 4) :
    ∀ x, deriv f x = 2 := by

  have h1 : f = fun x => 2 * (x - 1) - 4 := by
    funext x
    exact hf x

  intro x
  rw [h1]
  -- The derivative of $2(x - 1) - 4$ is 2.
  -- $2(x - 1) - 4 = 2x - 2 - 4 = 2x - 6$ is a linear function with slope 2.
  simp [deriv_const, deriv_id', mul_sub, sub_eq_add_neg, add_assoc]
  all_goals norm_num