import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_73367 : IsLeast {n : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x + y ≤ 1 ∧ n = x ^ 4 + y ^ 4 - x ^ 2 * y - x * y ^ 2} (-1 / 8) := by
  constructor
  · -- Show that -1/8 is achievable
    use 1 / 2, 1 / 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that -1/8 is the least element in the set
    intro n hn
    rcases hn with ⟨x, y, hx, hy, h2, heq⟩
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2),
      sq_nonneg (x^2 + y^2 - x * y), sq_nonneg (x^2 + y^2 - (x / 2) - (y / 2)), mul_pos hx hy, sq_nonneg (x - y), sq_nonneg (x^2 - y^2),
      sq_nonneg (x^2 + y^2 - 2 * x * y)]