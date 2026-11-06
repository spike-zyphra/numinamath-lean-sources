import Mathlib

open Real

theorem inequalities_75782 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) : a + b + c ≤ 3 := by
  have h1 : a + b + c ≤ 3 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          sq_nonneg (a * b + b * c + c * a - 1), h, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)
        ]
  linarith