import Mathlib

open Real

theorem inequalities_129275 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b + 1) * (a + b) ≥ 4 * a * b := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1), sq_nonneg (a * (b - 1)), sq_nonneg (b * (a - 1)), mul_nonneg ha hb]