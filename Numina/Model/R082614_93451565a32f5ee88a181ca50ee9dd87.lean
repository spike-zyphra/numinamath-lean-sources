import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_127654 :
  IsLeast {x | ∃ a b c d : ℝ, x = a^2 + b^2 + c^2 + d^2 ∧ a + 3 * b + 5 * c + 7 * d = 14} (7 / 3) := by
  constructor
  · -- proving 7/3 is obtained
    use 1 / 6, 1 / 2, 5 / 6, 7 / 6
    constructor
    · norm_num
    · norm_num
  · -- proving 7/3 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, h_eq2⟩
    have h1 : a^2 + b^2 + c^2 + d^2 ≥ 7 / 3 := by
      nlinarith [sq_nonneg (a - 1 / 6), sq_nonneg (b - 1 / 2), sq_nonneg (c - 5 / 6), sq_nonneg (d - 7 / 6),
        sq_nonneg (a + 3 * b + 5 * c + 7 * d - 14)]
    linarith [h_eq, h1]