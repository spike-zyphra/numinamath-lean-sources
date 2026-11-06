import Mathlib

open Real Set

theorem algebra_600279 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    a * b + b * c + c * a - 3 * a * b * c ≤ 1 / 4 := by
  have h1 : c = 1 - a - b := by linarith
  rw [h1] at *
  suffices a * b + b * (1 - a - b) + (1 - a - b) * a - 3 * a * b * (1 - a - b) ≤ 1 / 4 by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2),
          sq_nonneg ((1 - a - b) - 1 / 2), sq_nonneg (a + b - (1 - a - b)), 
          mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), 
          mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith)]