import Mathlib

theorem inequalities_216493 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 + a) ^ 4 * (1 + b) ^ 4 ≥ 64 * a * b * (a + b) ^ 2 := by 
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b - 2 * a * b), sq_nonneg (a * b - 1),
    sq_nonneg (a + b - 2), sq_nonneg (a * b), sq_nonneg (a + b - a * b), sq_nonneg (a ^ 2 + b ^ 2 - 2 * a * b),
    mul_nonneg ha hb, mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b ^ 2 by nlinarith),
    mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ a ^ 2 by nlinarith),
    mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ a * b by nlinarith),
    mul_nonneg (mul_nonneg ha hb) (show 0 ≤ a * b by nlinarith),
    mul_nonneg (show 0 ≤ (1 + a) ^ 2 by positivity) (show 0 ≤ (1 + b) ^ 2 by positivity)]