import Mathlib

theorem inequalities_240074 (a b c : ℝ) :
    (1 / 3) * (a + b + c) ^ 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a - b + 1) := by 
  nlinarith [sq_nonneg (a - b + 2), sq_nonneg (c - b + 1), sq_nonneg (a - c + 3), 
            sq_nonneg (a + b - c - 2), sq_nonneg (a - (c - 1) ), sq_nonneg ( (a - c ) /2 ), 
          sq_nonneg (a - (b - 2)), sq_nonneg (c - (b - 1)), mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (show (0 : ℝ) ≤ 2 by norm_num)
          ]