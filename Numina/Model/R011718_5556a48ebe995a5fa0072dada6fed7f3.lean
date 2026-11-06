import Mathlib

theorem inequalities_153814 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b ≤ 1) :
    9 * a ^ 2 * b + 9 * a * b ^ 2 - a ^ 2 - 10 * a * b - b ^ 2 + a + b ≥ 0 := by 
  have h1 : 0 < a * b := mul_pos ha hb
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 / 3), sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3),
          sq_nonneg (a * (b - 1 / 3)), sq_nonneg (b * (a - 1 / 3)), mul_pos ha hb,
          mul_nonneg (show 0 ≤ 1 - a - b by linarith) (show 0 ≤ a by linarith),
          mul_nonneg (show 0 ≤ 1 - a - b by linarith) (show 0 ≤ b by linarith),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)]