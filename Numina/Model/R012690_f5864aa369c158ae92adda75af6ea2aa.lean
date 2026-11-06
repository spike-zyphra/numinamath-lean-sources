import Mathlib

theorem inequalities_91475 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    (a^2 + b^2 + c^2)^2 + 6*a*b*c ≥ a*b + b*c + a*c := by
  have h1 : c = 1 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
            sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), sq_nonneg ((1 - a - b) - 1/2),
            mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith), 
            mul_nonneg (show 0 ≤ 1 - a - b by nlinarith) (show 0 ≤ (b) by linarith), mul_nonneg (show 0 ≤ 1 - a - b by nlinarith) (show 0 ≤ (a) by linarith),
            mul_nonneg (show 0 ≤ 1 - a - b by nlinarith) (show 0 ≤ (a * b) by nlinarith)]