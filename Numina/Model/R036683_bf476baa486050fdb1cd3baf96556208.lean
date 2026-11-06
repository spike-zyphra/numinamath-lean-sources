import Mathlib

theorem inequalities_599163 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a + 2 * a * b * c = 1) :
    a + b + c ≥ 2 * (a * b + b * c + c * a) := by
  have h1 : a + b + c ≥ 2 * (a * b + b * c + c * a) := by
    have h2 : a * b + b * c + c * a + 2 * a * b * c = 1 := h
    have h4 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)
      ]
  linarith