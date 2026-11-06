import Mathlib

theorem inequalities_596981 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 + b^3 + c^3 ≥ a^2 * b + b^2 * c + c^2 * a := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, 
      sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a)]