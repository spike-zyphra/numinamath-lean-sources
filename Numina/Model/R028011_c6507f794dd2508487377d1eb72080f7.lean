import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_101403 :
  IsLeast {f | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ f = 6 * (x ^ 2 + y ^ 2) * (x + y) -
    4 * (x ^ 2 + x * y + y ^ 2) - 3 * (x + y) + 5} 2 := by
  constructor
  · -- Show 2 exists, using x = y = 1/2.
    use (1 / 2), (1 / 2)
    norm_num
  · -- Show there is no smaller value.
    intro f h
    rcases h with ⟨x, y, hx, hy, heq⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2),
      sq_nonneg (x + y - 1), mul_pos hx hy, sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 1 / 4), sq_nonneg ((x + y) * 2 - 2)]