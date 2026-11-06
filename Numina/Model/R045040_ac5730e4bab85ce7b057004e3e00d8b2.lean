import Mathlib

theorem inequalities_600375 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 8) :
    16 * Real.sqrt 6 / 3 ≤ a^3 + b^3 + c^3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 2 * Real.sqrt 6 / 3), sq_nonneg (b - 2 * Real.sqrt 6 / 3), sq_nonneg (c - 2 * Real.sqrt 6 / 3),
          Real.sqrt_pos.mpr (show 0 < 6 by norm_num), Real.sq_sqrt (show 0 ≤ 6 by norm_num),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]