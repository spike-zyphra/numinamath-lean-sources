import Mathlib

theorem algebra_172831 (a b c : ℝ)
(ha : 0 ≤ a)
(hb : 0 ≤ b)
(hc : 0 ≤ c)
(h : a + b + c = 12) :
a * b + b * c + a * c + a * b * c ≤ 112 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
            mul_nonneg (show 0 ≤ a + b + c - a by linarith) (show 0 ≤ a + b + c - b by linarith), 
            mul_nonneg (show 0 ≤ a + b + c - c by linarith) (show 0 ≤ a + b + c - a by linarith)]