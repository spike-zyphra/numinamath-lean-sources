import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_73367 : IsLeast {n : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x + y ≤ 1 ∧ n = x ^ 4 + y ^ 4 - x ^ 2 * y - x * y ^ 2} (-1 / 8) := by
  constructor
  · -- $-1 / 8$ can be taken by $x = y = 1 / 2$
    use 1 / 2, 1 / 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · intro n h
    rcases h with ⟨x, y, hx, hy, hxy, hn⟩
    nlinarith [sq_nonneg (x + y - 1), sq_nonneg (x - y), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2)]