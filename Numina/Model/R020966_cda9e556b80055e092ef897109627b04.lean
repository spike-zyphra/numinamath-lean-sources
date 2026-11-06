import Mathlib

theorem inequalities_91123 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c ≥ 3) : a ^ 4 + b ^ 3 + c ^ 2 ≥ a ^ 3 + b ^ 2 + c := by
  nlinarith [sq_nonneg (a ^ 2 - a), sq_nonneg (b - 1), sq_nonneg (c - 1),
            sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            mul_nonneg ha (show (0 : ℝ) ≤ b by linarith),
            mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith),
            mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith),
            mul_nonneg ha (show (0 : ℝ) ≤ b by linarith),
            sq_nonneg (a + b + c - 3)]