import Mathlib

theorem inequalities_600142 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + 4 * a * b * c = 4) : a + b + c ≤ 3 := by
  have h1 : c ^ 2 = 4 - a^2 - b^2 - 4 * a * b * c := by
    nlinarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a + b + c - 2), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith), 
          mul_pos (show 0 < a * c by nlinarith) (show 0 < b by linarith)]