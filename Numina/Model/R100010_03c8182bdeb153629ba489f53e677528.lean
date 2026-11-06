import Mathlib

theorem inequalities_107628 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + 1) * (b + 1) * (c + 1) = 8) :
    3 ≤ a + b + c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]