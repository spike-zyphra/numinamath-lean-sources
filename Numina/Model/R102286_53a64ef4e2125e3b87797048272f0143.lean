import Mathlib

theorem inequalities_52913 (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) (h3 : c ≤ 3) :
    (a - b) * (a ^ 2 - 9) + (a - c) * (b ^ 2 - 9) + (b - c) * (c ^ 2 - 9) ≤ 36 := by
  have h1 : a ≤ 3 := by linarith
  have h2 : b ≤ 3 := by linarith

  nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 3), sq_nonneg (c - 3), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - a), sq_nonneg (c - b), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c),
     mul_nonneg (show (0 : ℝ) ≤ b - a by linarith) (show (0 : ℝ) ≤ c - b by linarith),
     mul_nonneg (show (0 : ℝ) ≤ a by assumption) (show (0 : ℝ) ≤ b - a by linarith),
     mul_nonneg (show (0 : ℝ) ≤ a by assumption) (show (0 : ℝ) ≤ c - a by linarith),
     mul_nonneg (show (0 : ℝ) ≤ b - a by linarith) (show (0 : ℝ) ≤ c - a by linarith)]