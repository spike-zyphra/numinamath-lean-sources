import Mathlib

theorem inequalities_302947 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 + b + 3 / 4) * (b^2 + c + 3 / 4) * (c^2 + a + 3 / 4) ≥
    (2 * a + 1 / 2) * (2 * b + 1 / 2) * (2 * c + 1 / 2) := by

  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
          sq_nonneg (a * b - 1 / 4), sq_nonneg (b * c - 1 / 4), sq_nonneg (c * a - 1 / 4),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]