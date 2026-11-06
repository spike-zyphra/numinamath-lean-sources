import Mathlib

theorem inequalities_276918 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a^3 + b^3) / 2 ≥ ((a + b) / 2)^3 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg (a - b),
    mul_pos ha hb, sq_nonneg (a^2 - b^2), sq_nonneg (a - b), sq_nonneg (a + b)]