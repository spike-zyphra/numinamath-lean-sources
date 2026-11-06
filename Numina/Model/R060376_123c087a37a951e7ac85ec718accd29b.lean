import Mathlib

theorem inequalities_66531 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (1 + a) * (1 + b) * (1 + c) ≥ 8 * (1 - a) * (1 - b) * (1 - c) := by 
  have h1 : c = 1 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by nlinarith), mul_pos hb (show 0 < 1 - a - b by nlinarith)]