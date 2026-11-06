import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_300364 :
  IsLeast {z : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ z = 6 * (x ^ 2 + y ^ 2) * (x + y) -
    4 * (x ^ 2 + x * y + y ^ 2) - 3 * (x + y) + 5} 2 := by
  constructor
  · -- Show that 2 belongs to the set
    use 1 / 2, 1 / 2
    norm_num
  · -- Show that any z in the set is ≥ 2
    intro z h
    rcases h with ⟨x, y, hx, hy, hz⟩
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2),
          sq_nonneg (x * y), sq_nonneg (x + y - 1),
          sq_nonneg (x - y), sq_nonneg (x * (y - 1/2)), sq_nonneg (y * (x - 1/2)), mul_pos hx hy
    ]