import Mathlib

theorem inequalities_599542 (a b : ℝ) (x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) : a * x ^ 2 + b * y ^ 2 ≥ (a * x + b * y) ^ 2 := by 
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb

  nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (x - y), sq_nonneg (a - b), sq_nonneg (a * (x - y)), sq_nonneg (b * (x - y)), 
           mul_pos ha hb, h]