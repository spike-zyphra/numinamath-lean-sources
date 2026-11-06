import Mathlib

theorem algebra_283088 :
    IsLeast {n : ℤ | ∃ a b c d : ℤ, n = a^2 + b^2 + c^2 + d^2 + a * b + c * d - a * c - b * d - b * c ∧ a * d - b * c = 1} 2 := by
  constructor
  · -- First, showing 2 is in the set
    use 1, 0, 0, 1
    all_goals norm_num
  · -- Now, showing that 2 is the smallest
    intro n hn
    rcases hn with ⟨a, b, c, d, h1, h2⟩
    nlinarith [sq_nonneg (a - 1), sq_nonneg (d - 1), sq_nonneg (b + c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a * b - c * d), sq_nonneg (a * d - b * c - 1), sq_nonneg (a + d - (b + c)), sq_nonneg (a - c - (b - d)), sq_nonneg (a * c - b * d)]