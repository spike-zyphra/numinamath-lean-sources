import Mathlib

theorem inequalities_6613 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 3) :
    12 ≤ (a + b) * (a + b * c) + (b + c) * (b + c * a) + (c + a) * (c + a * b) := by 
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
    h, mul_self_nonneg (a - b), mul_self_nonneg (a - c), mul_self_nonneg (b - c)]