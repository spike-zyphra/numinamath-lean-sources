import Mathlib

theorem algebra_9660 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 2023) :
    a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) ≥ 12138 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a * a - b * b), sq_nonneg (b * b - c * c), sq_nonneg (c * c - a * a),
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
  ]