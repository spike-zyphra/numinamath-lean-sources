import Mathlib
theorem algebra_23908 (a b c d : ℝ) (h1 : a + b + c + d = 6) (h2 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 12) :
36 ≤ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ∧ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 48:= by
  constructor
  · -- First, prove 36 ≤ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4)
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 3),
      sq_nonneg (a - 3), sq_nonneg (b - 3), sq_nonneg (c - 3), sq_nonneg (d - 1),
      h1, h2, 
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1)]
  · -- Now, prove 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 48
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (d - 0),
      sq_nonneg (a - 0), sq_nonneg (b - 0), sq_nonneg (c - 0), sq_nonneg (d - 2),
      h1, h2, 
      sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (d - 2)]