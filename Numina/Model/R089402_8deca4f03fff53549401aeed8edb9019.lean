import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_600590 :
  IsGreatest {s : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 ∧ s = 2 * x ^ 2 + y + 3 * z ^ 2} 3 ∧
  IsLeast {s : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 ∧ s = 2 * x ^ 2 + y + 3 * z ^ 2} (57 / 72) := by
  constructor
  · -- Proof that 3 is greatest
    constructor
    · -- Show it's attained
      use 0, 0, 1
      norm_num
    · -- Show it's greatest
      intro s hs
      rcases hs with ⟨x, y, z, hx, hy, hz, hsum, hs⟩
      nlinarith [sq_nonneg (z - 1), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x + y + z - 1)]
  · -- Proof that 57/72 is least
    constructor
    · -- Show it's attained
      use 1 / 4, 7 / 12, 1 / 6
      constructor
      norm_num
      constructor
      norm_num
      constructor
      norm_num
      constructor
      norm_num
      norm_num
    · -- Show it's least
      intro s hs
      rcases hs with ⟨x, y, z, hx, hy, hz, hsum, hs⟩
      nlinarith [sq_nonneg (x - 1/4), sq_nonneg (y - 7/12), sq_nonneg (z - 1/6), sq_nonneg (x + y + z - 1)]