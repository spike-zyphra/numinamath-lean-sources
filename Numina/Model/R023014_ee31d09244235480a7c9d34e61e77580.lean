import Mathlib

theorem inequalities_7057 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = 3) :
    a ^ 5 + b ^ 5 + c ^ 5 ≥ a ^ 3 + b ^ 3 + c ^ 3 := by
  nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (c ^ 2 - 1),
            sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]