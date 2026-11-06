import Mathlib

theorem inequalities_600947
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a * b * c ≥ (-a + b + c) * (a - b + c) * (a + b - c) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (a + c - b),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]