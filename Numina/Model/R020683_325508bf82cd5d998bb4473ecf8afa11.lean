import Mathlib

theorem inequalities_597076 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 4) :
    a^3 + b^3 + c^3 + d^3 ≤ 8 := by
  have h1 : a ≤ 2 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), h]
  have h1' : a ≥ -2 := by
    nlinarith [sq_nonneg (a + 2), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), h]
  have h2 : b ≤ 2 := by
    nlinarith [sq_nonneg (b - 2), sq_nonneg (a), sq_nonneg (c), sq_nonneg (d), h]
  have h2' : b ≥ -2 := by
    nlinarith [sq_nonneg (b + 2), sq_nonneg (a), sq_nonneg (c), sq_nonneg (d), h]
  have h3 : c ≤ 2 := by
    nlinarith [sq_nonneg (c - 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (d), h]
  have h3' : c ≥ -2 := by
    nlinarith [sq_nonneg (c + 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (d), h]
  have h4 : d ≤ 2 := by
    nlinarith [sq_nonneg (d - 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), h]
  have h4' : d ≥ -2 := by
    nlinarith [sq_nonneg (d + 2), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), h]
  have h5 : a ^ 3 ≤ 2 * a ^ 2 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a), h1, h1']
  have h6 : b ^ 3 ≤ 2 * b ^ 2 := by
    nlinarith [sq_nonneg (b - 2), sq_nonneg (b), h2, h2']
  have h7 : c ^ 3 ≤ 2 * c ^ 2 := by
    nlinarith [sq_nonneg (c - 2), sq_nonneg (c), h3, h3']
  have h8 : d ^ 3 ≤ 2 * d ^ 2 := by
    nlinarith [sq_nonneg (d - 2), sq_nonneg (d), h4, h4']
  have h9 : a^3 + b^3 + c^3 + d^3 ≤ 2 * (a^2 + b^2 + c^2 + d^2) := by
    linarith [h5, h6, h7, h8]
  linarith [h9, h]