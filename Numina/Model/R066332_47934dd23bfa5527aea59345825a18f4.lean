import Mathlib

theorem algebra_306924 (a b c : ℝ) (h : a + b + c = a ^ 2 + b ^ 2 + c ^ 2) :
    a + b + c ≤ 3 ∧ ∃ a b c, a + b + c = 3 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 3 := by
  constructor
  · -- First, let's prove that a + b + c ≤ 3
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  · -- Now, let's show the existence of a, b, c such that a + b + c = 3 and a^2 + b^2 + c^2 = 3
    use 1, 1, 1
    constructor
    · -- Check a + b + c = 3
      norm_num
    · -- Check a^2 + b^2 + c^2 = 3
      norm_num