import Mathlib

open Real

theorem inequalities_602281 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    sqrt a + sqrt b + sqrt c ≥ a * b + b * c + c * a := by
  nlinarith [sq_nonneg (sqrt a - 1), sq_nonneg (sqrt b - 1), sq_nonneg (sqrt c - 1),
          Real.sq_sqrt (show 0 ≤ a by linarith),
          Real.sq_sqrt (show 0 ≤ b by linarith),
          Real.sq_sqrt (show 0 ≤ c by linarith),
          Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
          mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c),
          mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]