import Mathlib

theorem inequalities_310478 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    Real.sqrt a + Real.sqrt b + Real.sqrt c ≥ a * b + b * c + c * a := by
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
          sq_nonneg (Real.sqrt a - 1), sq_nonneg (Real.sqrt b - 1), sq_nonneg (Real.sqrt c - 1),
          Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith),
          Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith),
          Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]