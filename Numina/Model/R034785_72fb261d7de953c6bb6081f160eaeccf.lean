import Mathlib

theorem inequalities_318827 (a b c : ℝ) (ha : 0 ≤ c) (hc : c ≤ b) (hb : b ≤ a)
    (h : a + b + c = 3) :
    a * b ^ 2 + b * c ^ 2 + c * a ^ 2 ≤ 27 / 8 := by

  have h1 : c ≤ a := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
          sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 0),
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ b - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b - c by linarith) (show (0 : ℝ) ≤ a - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ a - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a - b by linarith) (show (0 : ℝ) ≤ a - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ c by linarith)
         ]