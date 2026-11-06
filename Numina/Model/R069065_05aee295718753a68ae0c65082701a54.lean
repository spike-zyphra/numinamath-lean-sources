import Mathlib

theorem inequalities_189929 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b * (a + b) + b * c * (b + c) + a * c * (a + c) ≥ 6 * a * b * c := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a * c := mul_pos ha hc
  have h3 : 0 < b * c := mul_pos hb hc
  have h4 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith), 
          mul_pos (show 0 < a by linarith) (show 0 < c by linarith)]