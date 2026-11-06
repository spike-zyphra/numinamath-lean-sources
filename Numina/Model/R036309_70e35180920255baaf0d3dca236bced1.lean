import Mathlib

theorem inequalities_601765 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    2 * (a ^ 3 + b ^ 3 + c ^ 3) + a * b * c + a * b + b * c + c * a + 2 ≥
    2 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + a ^ 2 + b ^ 2 + c ^ 2 + a + b + c := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
            sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
            mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith), 
            mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)]