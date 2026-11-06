import Mathlib

open Real Set
open scoped Real

theorem algebra_179756 (α : ℝ) :
  sin (3 * α) = 3 * sin α - 4 * (sin α)^3 := by
  rw [sin_three_mul]
  all_goals ring