import Mathlib

theorem inequalities_237371 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^2 * b + a * b^2 ≤ a^3 + b^3 := by 
  nlinarith [sq_nonneg (a - b), mul_pos ha hb, sq_nonneg (a + b), sq_nonneg (a - b)]