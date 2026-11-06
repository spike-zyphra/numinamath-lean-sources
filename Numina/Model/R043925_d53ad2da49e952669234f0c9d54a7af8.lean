import Mathlib
set_option maxHeartbeats 800000
theorem inequalities_601031 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 2) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + a * b * c ≤ 1 := by
  have h1 : c = 2 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), 
          sq_nonneg (a + b - (2 - a - b)), mul_pos ha hb, 
          mul_pos hb (show 0 < 2 - a - b by nlinarith), 
          mul_pos ha (show 0 < 2 - a - b by nlinarith), 
          sq_nonneg (a + b - 1), sq_nonneg ((2 - a - b) - 1)]