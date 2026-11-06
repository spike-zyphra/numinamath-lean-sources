import Mathlib

theorem inequalities_42875 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a^3 + b^3 + c^3 + 6 ≥ (a + b + c)^2 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b + c - 3), 
    sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]