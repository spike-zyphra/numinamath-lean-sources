import Mathlib

theorem inequalities_52451 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    a^2 + b^2 + c^2 ≥ 4 * (a * b + b * c + c * a) - 1 := by 
  have h1 : c = 1 - a - b := by linarith 
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ (1 - a - b) by nlinarith), 
          mul_nonneg ha (show 0 ≤ (1 - a - b) by nlinarith)]