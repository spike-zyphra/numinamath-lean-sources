import Mathlib

theorem inequalities_108842 (a b c d e : ℝ) (ha : 0 ≤ a) (h : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e)
    (h1 : a + b + c + d + e = 1) :
    a * d + d * c + c * b + b * e + e * a ≤ 1 / 5 := by 
  nlinarith [sq_nonneg (a + b - 2 * c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - e), sq_nonneg (a + b + c + d - 4 * e)]