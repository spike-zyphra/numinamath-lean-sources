import Mathlib

theorem algebra_598717 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : a * b * c + 2 * a^2 + 2 * b^2 + 2 * c^2 + c * a - b * c - 4 * a + 4 * b - c = 28) :
    a + b + c ≤ 6 := by
  nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 1), sq_nonneg (c - 2), 
    sq_nonneg (a * b - 3), sq_nonneg (b * c - 2), sq_nonneg (c * a - 6),
    mul_nonneg (show 0 ≤ a - 1 by linarith) (show 0 ≤ b - 1 by linarith),
    mul_nonneg (show 0 ≤ a - 1 by linarith) (show 0 ≤ c - 1 by linarith), 
    mul_nonneg (show 0 ≤ b - 1 by linarith) (show 0 ≤ c - 1 by linarith), 
    mul_nonneg (show 0 ≤ a - 1 by linarith) (show 0 ≤ (c - 1) by linarith)
  ]