import Mathlib

theorem inequalities_214436 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b > a + b) : 4 < a + b := by 
  by_contra h1
  push_neg at h1
  nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a - b),
          sq_nonneg (a * b - 4), mul_pos ha hb, mul_nonneg ha.le hb.le ]