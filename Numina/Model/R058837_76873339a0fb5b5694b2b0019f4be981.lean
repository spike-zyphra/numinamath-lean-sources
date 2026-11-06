import Mathlib

theorem inequalities_603343 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a^5 + b^5 = a^3 + b^3) :
    a^2 + b^2 ≤ 1 + a * b := by
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a * b - 1), mul_pos ha hb]