import Mathlib

theorem inequalities_45140 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c * (a + b + c) = 3) :
    (a + b) * (b + c) * (c + a) ≥ 8 := by
  have h2 : (a + b) * (b + c) * (c + a) = (a * b + b * c + c * a) * (a + b + c) - (a * b * c) := by
    ring
  rw [h2]
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
          sq_nonneg (a * b + b * c + c * a - 3),
          sq_nonneg (a + b + c - 3),
          sq_nonneg (a * b * c - 1),
          mul_nonneg (show 0 ≤ a * b * c by positivity) (show 0 ≤ (a + b + c) by positivity),
          sq_nonneg (a * b * (a * b * c * (a + b + c) - 3) ) ]