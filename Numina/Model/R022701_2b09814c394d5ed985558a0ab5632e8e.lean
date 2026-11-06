import Mathlib

theorem inequalities_602028 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    6 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) ≥
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) + 1 / 8 := by
  have h1 : d = 1 - a - b - c := by
    linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - (1 - a - b - c)), sq_nonneg (b - c), sq_nonneg (b - (1 - a - b - c)), sq_nonneg (c - (1 - a - b - c)), 
          sq_nonneg (a + b + c - 3 / 4), sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4), sq_nonneg (c - 1 / 4), sq_nonneg ((1 - a - b - c) - 1 / 4),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha (show 0 < (1 - a - b - c) by nlinarith), 
          mul_pos hb hc, mul_pos hb (show 0 < (1 - a - b - c) by nlinarith), 
          mul_pos hc (show 0 < (1 - a - b - c) by nlinarith)
        ]