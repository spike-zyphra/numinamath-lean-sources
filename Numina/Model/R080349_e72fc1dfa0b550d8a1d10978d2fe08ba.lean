import Mathlib

open Real
open scoped BigOperators

theorem calculus_13137 (v w : ℝ × ℝ)
  (h₀ : v = (5, -3)) (h₁ : w = (11, -2)) :
  abs (v.1 * w.2 - w.1 * v.2) = 23 := by
  rw [h₀, h₁]
  norm_num [abs_of_nonneg]
  all_goals norm_num