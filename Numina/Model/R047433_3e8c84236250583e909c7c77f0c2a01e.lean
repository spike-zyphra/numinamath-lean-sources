import Mathlib

theorem inequalities_187993 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (2 * a + b) * (2 * a - b) * (a - c) + (2 * b + c) * (2 * b - c) * (b - a) +
    (2 * c + a) * (2 * c - a) * (c - b) ≥ 0 := by 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)),
          sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]