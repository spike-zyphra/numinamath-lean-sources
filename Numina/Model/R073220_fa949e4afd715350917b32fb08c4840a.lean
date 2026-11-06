import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_307458 :
  IsLeast {u : ℝ | ∃ x y, u = x^2 + y^2 + 6 * x - 2 * y ∧ 3 * x + 2 * y - 1 ≥ 0} (-66 / 13) := by
  constructor
  · -- Show that -66/13 is achievable, by finding specific x and y
    use -15 / 13, 29 / 13
    norm_num
  · -- Show for all u in the set, -66/13 ≤ u
    intro u
    rintro ⟨x, y, h_eq, h_ineq⟩
    have h : (x + 3) ^ 2 + (y - 1) ^ 2 ≥ (64 / 13) := by
      nlinarith [sq_nonneg (x + 15 / 13), sq_nonneg (y - 29 / 13),
        h_ineq, 
        sq_nonneg (3 * x + 2 * y - 1)]
    nlinarith [h]