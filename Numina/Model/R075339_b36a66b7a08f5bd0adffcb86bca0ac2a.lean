import Mathlib

theorem inequalities_237287 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 1) :
    (1 + a) * (1 + b) * (1 + c) ≥ 8 * (1 - a) * (1 - b) * (1 - c) := by
  have ha1 : c = 1 - a - b := by linarith
  rw [ha1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - (1 - a - b)), sq_nonneg (a - (1 - a - b)), 
           mul_nonneg ha hb, 
           mul_nonneg hb (show 0 ≤ 1 - a - b by nlinarith), 
           mul_nonneg ha (show 0 ≤ 1 - a - b by nlinarith),
           mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
           mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 1 - a - b by nlinarith), 
           mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 - a - b by nlinarith)]