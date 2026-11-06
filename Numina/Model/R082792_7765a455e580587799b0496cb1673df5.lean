import Mathlib

open Real
open scoped Real

theorem calculus_16481 : cos (6 * arccos (1 / 3)) = 329 / 729 := by
  have h1 : cos (arccos (1 / 3)) = 1 / 3 := by
    exact cos_arccos (by norm_num) (by norm_num)
  have h2 : cos (3 * arccos (1 / 3)) = -23 / 27 := by
    have h3 : cos (3 * arccos (1 / 3)) = 4 * (cos (arccos (1 / 3)))^3 - 3 * (cos (arccos (1 / 3))) := by
      rw [cos_three_mul]
    rw [h3]
    rw [h1]
    norm_num
  have h4 : cos (6 * arccos (1 / 3)) = 2 * (cos (3 * arccos (1 / 3)))^2 - 1 := by
    have h5 : cos (6 * arccos (1 / 3)) = cos (2 * (3 * arccos (1 / 3))) := by ring
    rw [h5]
    rw [cos_two_mul]
    all_goals norm_num
  rw [h4, h2]
  norm_num