import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_147614 :
  IsGreatest {M | ∃ x y z : ℝ, M = 7 * x + 10 * y + z ∧ x ^ 2 + 2 * x + (1 / 5) * y ^ 2 + 7 * z ^ 2 = 6} 55 := by
  constructor
  · -- Show 55 is in the set
    use (-13 / 62), (175 / 31), (1 / 62)
    constructor
    · -- Show M = 55
      norm_num
    · -- Show the constraint is satisfied
      norm_num
  · -- Show that 55 is the greatest
    intro M h
    rcases h with ⟨x, y, z, h1, h2⟩
    nlinarith [sq_nonneg (x + 13 / 62), sq_nonneg (y - 175 / 31), sq_nonneg (z - 1 / 62),
      sq_nonneg (x + 13 / 62), sq_nonneg (y + 175 / 31), sq_nonneg (z + 1 / 62)]