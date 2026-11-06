import Mathlib

open Real Set
open scoped Real

theorem algebra_243277 : cos (3 * π / 180) < cos (π / 180) := by
  have h1 : 0 < π / 180 := by
    linarith [Real.pi_pos]
  have h2 : π / 180 < 3 * π / 180 := by
    linarith [Real.pi_pos]
  have h3 : 3 * π / 180 < π := by
    linarith [Real.pi_pos]
  have h4 : cos (3 * π / 180) < cos (π / 180) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    all_goals
      linarith [Real.pi_pos]
  exact h4