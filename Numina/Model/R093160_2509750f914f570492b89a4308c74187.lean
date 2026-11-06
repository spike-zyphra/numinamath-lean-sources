import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_234525 :
  IsGreatest {x | ∃ a b : ℝ, x = a^2 * b - b^2 * a ∧ 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1} (1/4) := by
  constructor
  · -- Show that 1/4 is in the set. Let a = 1 and b = 1/2
    use 1, 1 / 2
    constructor
    · -- Show the result is 1/4
      norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Now, we have to prove that 1/4 is greatest
    intro x hx
    rcases hx with ⟨a, b, heq, ha0, ha1, hb0, hb1⟩
    have h1 : a ^ 2 * b - b ^ 2 * a ≤ 1 / 4 := by
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (a - b), sq_nonneg (a + b - 1), mul_nonneg (sub_nonneg.mpr ha0) (sub_nonneg.mpr hb0), mul_nonneg (sub_nonneg.mpr ha0) (sub_nonneg.mpr (show (1 : ℝ) - a ≥ 0 by linarith)), mul_nonneg (sub_nonneg.mpr hb0) (sub_nonneg.mpr (show (1 : ℝ) - b ≥ 0 by linarith))]
    linarith [heq, h1]