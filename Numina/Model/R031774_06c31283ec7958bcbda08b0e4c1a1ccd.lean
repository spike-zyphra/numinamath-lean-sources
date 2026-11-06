import Mathlib

theorem inequalities_58034 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c ≤ a + b + c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ Real.sqrt 3 * a * b * c := by 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          Real.sqrt_nonneg 3, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0),
          sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2 - Real.sqrt 3 * a * b * c),
          sq_nonneg (a + b + c - a * b * c),
          mul_pos (show 0 < a by linarith) (show 0 < b by linarith),
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith),
          mul_pos (show 0 < a by linarith) (show 0 < c by linarith)
        ]