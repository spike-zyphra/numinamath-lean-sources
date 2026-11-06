import Mathlib

theorem inequalities_602301 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2) ≥ 3 * (a + b + c) ^ 2 := by 
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * b + a * c + b * c - 3), sq_nonneg (a + b + c - 3),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]