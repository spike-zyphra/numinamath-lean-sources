import Mathlib

theorem inequalities_84708
    (a b c : ℝ)
    (h : a^2 * b^2 + 18 * a * b * c > 4 * b^3 + 4 * a^3 * c + 27 * c^2) :
    a^2 > 3 * b := by
  nlinarith [sq_nonneg (c * 9 - a ^ 2 * 2 + a * b * 3), sq_nonneg (a ^ 2 - 3 * b), sq_nonneg (a ^ 2 - 3 * b - 2 * a * b), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c - (18 * a * b - 4 * a ^ 3) / 54), sq_nonneg (a ^ 2 - 3 * b - c), sq_nonneg (a ^ 2 - 3 * b + 2 * c), sq_nonneg (a * b - 3 * b ^ 2 / 2), sq_nonneg (a * b + a ^ 2 - 3 * b), sq_nonneg (c + (a ^ 2 - 3 * b) * 3 * a / 9), sq_nonneg (c - (a ^ 2 - 3 * b) * a / 3), sq_nonneg (c - (a ^ 2 - 3 * b) * a / 2), sq_nonneg (c + (a ^ 2 - 3 * b) * a / 2), sq_nonneg (c - (a ^ 2 - 3 * b) ^ 2 / (2 * 3 * a)), sq_nonneg (c - (a ^ 2 * a * 1 / 2)), sq_nonneg (a ^ 2 - 3 * b * 1 / 2), sq_nonneg (c - (a ^ 2 * b * 1 / 2)), sq_nonneg (c - (b * a * 1 / 2)), sq_nonneg (c - (a ^ 2 * a * 1 / 2)), sq_nonneg (a ^ 2 - 3 * b * 1 / 4)]