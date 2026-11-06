import Mathlib

theorem inequalities_5034 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 3) :
    a^3 + b^3 + c^3 + 8*(a*b+b*c+c*a) ≤ 27 := by
  have h1 : c = 3 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - (3 - a - b)), sq_nonneg (a - (3 - a - b)), 
    mul_nonneg ha hb, 
    mul_nonneg hb (show 0 ≤ (3 - a - b) by nlinarith), 
    mul_nonneg ha (show 0 ≤ (3 - a - b) by nlinarith), 
    sq_nonneg (a + b - (3 - a - b)), 
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((3 - a - b) - 1)]