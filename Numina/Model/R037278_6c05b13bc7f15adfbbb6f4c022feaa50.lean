import Mathlib

theorem inequalities_603843 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 3) :
    a^3 * (b + c) + b^3 * (c + a) + c^3 * (a + b) ≤ 6 := by
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)),
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]