import Mathlib

theorem inequalities_3305
    (a b m n : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (hn : 0 < n) :
    (2 * a * m + m ^ 2) * (2 * b * n + n ^ 2) ≤ (a * n + b * m + m * n) ^ 2 := by
  nlinarith [sq_nonneg (a * n - b * m), sq_nonneg (a * m - b * n), 
          sq_nonneg (a * n - b * m), sq_nonneg (a * m - b * n), 
          sq_nonneg (a - b), sq_nonneg (m - n), 
          sq_nonneg (m * a - n * a), sq_nonneg (m * b - n * b), 
          mul_pos ha hb, mul_pos ha hm, mul_pos ha hn, 
          mul_pos hb hm, mul_pos hb hn, 
          mul_pos hm hn
        ]