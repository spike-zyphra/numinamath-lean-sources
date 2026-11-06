import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_319804 :
  IsGreatest {x + y - x * y | (x : ℝ) (y : ℝ) (h : x ^ 2 + y ^ 2 ≤ 1)} 1 := by
  constructor
  · use 0, 1
    norm_num
  · -- Show that any value in the set is ≤ 1.
    intro z hz
    rcases hz with ⟨x, y, h, hz⟩
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1),
      sq_nonneg (x + y - 1), mul_self_nonneg (x - y)]