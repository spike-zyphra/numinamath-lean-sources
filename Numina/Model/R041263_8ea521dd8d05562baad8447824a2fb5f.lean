import Mathlib

theorem inequalities_198277 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a > a + b + c) : 3 < a + b + c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]