import Mathlib

open Real
open scoped BigOperators

theorem inequalities_242329 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  2 * (a + b + c) * (a * b + b * c + c * a) ≤
  (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) + 9 * a * b * c := by

  have h2 : (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a + b + c) * (a * b + b * c + c * a) + 9 * a * b * c ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c by assumption),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos ha (show 0 < b * c by nlinarith), 
          mul_pos hb (show 0 < a * c by nlinarith), 
          mul_pos hc (show 0 < a * b by nlinarith)
        ]
  linarith [h2]