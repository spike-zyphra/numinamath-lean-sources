import Mathlib

theorem inequalities_603474 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 2) :
    a ^ 4 + b ^ 4 + c ^ 4 + a * b * c ≥ a ^ 3 + b ^ 3 + c ^ 3 := by
  have h1 : c = 2 - a - b := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), 
    sq_nonneg (a + b - (2 - a - b)), 
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((2 - a - b) - 1), 
    mul_nonneg ha hb, mul_nonneg hb (show (0 : ℝ) ≤ 2 - a - b by nlinarith), 
    mul_nonneg ha (show (0 : ℝ) ≤ 2 - a - b by nlinarith)]