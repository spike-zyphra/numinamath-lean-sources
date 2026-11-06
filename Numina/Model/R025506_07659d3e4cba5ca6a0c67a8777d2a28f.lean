import Mathlib

theorem inequalities_304216
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a + b) * (b + c) * (c + a) ≥ 4 * (a + b + c - 1) := by 
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
            sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]