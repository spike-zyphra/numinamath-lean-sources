import Mathlib

theorem inequalities_114433 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) * (b + c) * (c + a) ≥ 8 * a * b * c := by
  nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c by linarith),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), mul_pos ha (show 0 < b * c from mul_pos hb hc), mul_pos hb (show 0 < a * c from mul_pos ha hc)]