import Mathlib

theorem inequalities_603093 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 2) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≤ 2 := by
  have h1 : c = 2 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), 
            mul_nonneg ha hb, mul_nonneg ha (show 0 ≤ 2 - a - b by nlinarith), 
            mul_nonneg hb (show 0 ≤ 2 - a - b by nlinarith), 
            sq_nonneg (a + b - (2 - a - b)), 
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 2 - a - b by nlinarith), 
            mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 2 - a - b by nlinarith), 
            sq_nonneg (a * b - b * (2 - a - b)), 
            sq_nonneg (b * (2 - a - b) - (2 - a - b) * a), 
            sq_nonneg (a * b - (2 - a - b) * a)]