import Mathlib

theorem algebra_14281 :
    IsLeast {n : ℝ | ∃ x y, n = 2 * x ^ 2 + 2 * x * y + y ^ 2 - 2 * x + 2 * y + 4} (-1) := by
  constructor
  · -- Let's prove that -1 is in the set
    use 2, -3
    norm_num
  · -- Let's show that -1 is a lower bound
    intro n hn
    rcases hn with ⟨x, y, h_eq⟩
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 3), sq_nonneg (x + (y - 1) / 2), sq_nonneg (y + 3), sq_nonneg (2 * x + y - 1), sq_nonneg (x + y + 1)]