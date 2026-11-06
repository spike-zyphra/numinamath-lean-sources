import Mathlib

theorem inequalities_4057 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 2) :
    a * b * c * (a + b + c + 9 * a * b * c) ≤ 4 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : a * b * c * (a + b + c + 9 * a * b * c) - 4 ≤ 0 := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a + b + c - 2), sq_nonneg (a * b + b * c + c * a - 2), 
          sq_nonneg (a * b * c), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith), 
          mul_pos (show 0 < a * b from by nlinarith) (show 0 < c * a from by nlinarith), 
          mul_pos (show 0 < b * c from by nlinarith) (show 0 < c * a from by nlinarith)
        ]
  linarith