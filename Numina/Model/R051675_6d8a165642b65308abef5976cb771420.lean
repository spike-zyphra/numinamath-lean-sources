import Mathlib

theorem inequalities_6916
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hsum : a + b + c = 3) :
    a + a * b + a * b * c ≤ 4 := by

  have ha' : c = 3 - a - b := by linarith
  
  rw [ha']
  
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a + b - 1), sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a * (3 - a - b)), sq_nonneg (b * (3 - a - b)), mul_nonneg ha hb, mul_nonneg hb (show 0 ≤ (3 - a - b) by nlinarith)]