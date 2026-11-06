import Mathlib

theorem inequalities_598190
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a * b * c ≥ (-a + b + c) * (a - b + c) * (a + b - c) := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]