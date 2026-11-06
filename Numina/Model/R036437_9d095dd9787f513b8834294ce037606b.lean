import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_221394 :
  IsGreatest {a | ∃ x y : ℝ, a = x^4 * y + x * y^4 + x^3 * y + x * y^3 + x^2 * y + x * y^2 ∧ x + y = 1} (7 / 16) := by
  constructor
  · -- Show 7/16 is in the set
    use 1 / 2, 1 / 2
    constructor
    · -- Show the value of the expression equals 7/16
      norm_num
    · -- Show x + y = 1
      norm_num
  · -- Show that 7/16 is the greatest in the set
    intro a ha
    rcases ha with ⟨x, y, h_eq, h_sum⟩
    have h1 : y = 1 - x := by linarith
    rw [h1] at h_eq
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x * (x - 1 / 2)), sq_nonneg ((1 - x) * (x - 1 / 2)), sq_nonneg (x * (1 - x) - 1 / 4), sq_nonneg ((x - 1 / 2) * (x * (1 - x))), sq_nonneg ((x - (1 - x))), sq_nonneg ((x * (1 - x)) - 1 / 4), sq_nonneg ((x^2 - (1 - x)^2)), sq_nonneg ((x * (1 - x)) - 1 / 4)]