import Mathlib

theorem inequalities_598313 (a b c d e f : ℝ) (h : a + b + c + d + e + f = 0) :
    a * b + b * c + c * d + d * e + e * f + f * a ≤ (1 / 2) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2) := by
  nlinarith [sq_nonneg (a + b + c + d + e + f), sq_nonneg (a - b + c - d + e - f), sq_nonneg (a + d - b - e), sq_nonneg (a + d - c - f), sq_nonneg (b + e - c - f), sq_nonneg (a + f - c - d), sq_nonneg (b + f - a - d), sq_nonneg (e + b - c - d)]