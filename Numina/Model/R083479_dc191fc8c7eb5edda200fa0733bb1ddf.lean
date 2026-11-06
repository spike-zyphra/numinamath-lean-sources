import Mathlib

theorem inequalities_276936 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c)^3 - (a^3 + b^3 + c^3) > (a + b) * (b + c) * (a + c) := by
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]