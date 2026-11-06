import Mathlib

theorem inequalities_318927 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = a + b + c) :
    5 ≤ a^2 + b^2 + c^2 + 2 * a * b * c := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (mul_pos ha hb) hc
        ]