import Mathlib

theorem inequalities_277098 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) * (b + c) * (c + a) ≥ 8 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, 
          mul_pos ha hc, mul_pos hb ha, mul_pos hb hc, mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith), 
          mul_pos (show 0 < c by linarith) (show 0 < a by linarith)]