import Mathlib

theorem inequalities_199501 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a ≥ 12) : 6 ≤ a + b + c := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]