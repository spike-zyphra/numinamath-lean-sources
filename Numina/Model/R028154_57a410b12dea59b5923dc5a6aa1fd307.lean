import Mathlib

theorem inequalities_71142 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a ^ 3 + b ^ 3 + c ^ 3 + 2 * ((a * b) ^ 3 + (b * c) ^ 3 + (c * a) ^ 3) ≥
    3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
            sq_nonneg (a * (a - b) + b * (b - c) + c * (c - a)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]