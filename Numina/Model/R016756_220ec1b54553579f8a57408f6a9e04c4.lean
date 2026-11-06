import Mathlib

theorem inequalities_297519 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    10 * (a^3 + b^3 + c^3) - 9 * (a^5 + b^5 + c^5) ≥ 1 := by
  have h1 : c = 1 - a - b := by linarith
  rw [h1]
  suffices 10 * (a ^ 3 + b ^ 3 + (1 - a - b) ^ 3) - 9 * (a ^ 5 + b ^ 5 + (1 - a - b) ^ 5) - 1 ≥ 0 by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
            sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg ((1 - a - b) - 1/3),
            mul_pos ha hb, mul_pos hb (show 0 < 1 - a - b by nlinarith), mul_pos ha (show 0 < 1 - a - b by nlinarith),
            sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - (1 - a - b)^2), sq_nonneg (b^2 - (1 - a - b)^2)]