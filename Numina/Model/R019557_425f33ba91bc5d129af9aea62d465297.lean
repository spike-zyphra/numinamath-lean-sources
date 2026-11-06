import Mathlib

theorem inequalities_599118 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a + 2 * a * b * c = 1) : 3 / 4 ≤ a * b + b * c + c * a := by

  have h2 : a * b + b * c + c * a ≥ 3 / 4 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
      mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)
    ]
  linarith