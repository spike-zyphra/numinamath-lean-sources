import Mathlib

open Real

theorem inequalities_604127 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    sqrt a + sqrt b + sqrt c ≥ a * b + b * c + c * a := by
  nlinarith [sq_nonneg (sqrt a - 1), sq_nonneg (sqrt b - 1), sq_nonneg (sqrt c - 1),
          Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
          Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ c by linarith),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
          mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c),
          mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          h,
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
  ]