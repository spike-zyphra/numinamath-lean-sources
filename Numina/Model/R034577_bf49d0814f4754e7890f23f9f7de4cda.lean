import Mathlib

open Real

theorem inequalities_176714 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    sqrt (4 * a + 1) + sqrt (4 * b + 1) + sqrt (4 * c + 1) < 5 := by
  nlinarith [sq_nonneg (sqrt (4 * a + 1) - 2), sq_nonneg (sqrt (4 * b + 1) - 2), sq_nonneg (sqrt (4 * c + 1) - 2),
          Real.sqrt_nonneg (4 * a + 1), Real.sqrt_nonneg (4 * b + 1), Real.sqrt_nonneg (4 * c + 1),
          Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * b + 1 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * c + 1 by nlinarith),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
]