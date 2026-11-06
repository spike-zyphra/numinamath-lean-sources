import Mathlib

open Real

theorem inequalities_297288 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ a * b * c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ sqrt 3 * a * b * c := by 
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2 - sqrt 3 * a * b * c), 
          sq_nonneg (a * b * c), 
          sq_nonneg (a + b + c - a * b * c), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]