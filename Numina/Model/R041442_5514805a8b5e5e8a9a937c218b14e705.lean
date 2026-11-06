import Mathlib

theorem inequalities_44634 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a + 2 * a * b * c = 1) :
    4 * a + b + c ≥ 2 := by
  have h1 : 0 < a * b * c := by
    positivity
  nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - c), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * c by nlinarith) (show 0 < b * c by nlinarith)]