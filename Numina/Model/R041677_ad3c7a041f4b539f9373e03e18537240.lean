import Mathlib

theorem inequalities_83978 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + b) * (a + c) * (b + c) = 1) :
    a * b + b * c + c * a ≤ 3 / 4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b + c - 3 / 2),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (mul_pos ha hb) hc
        ]