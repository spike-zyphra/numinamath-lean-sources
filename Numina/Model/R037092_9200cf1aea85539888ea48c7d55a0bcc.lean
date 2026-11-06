import Mathlib

theorem inequalities_601884 (a b c : ℝ) :
    (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4 ≥
    4 / 7 * (a + b + c) ^ 4 := by 
  nlinarith [sq_nonneg ( (a + b) ^ 2 - (b + c) ^ 2 ), sq_nonneg ( (b + c) ^ 2 - (c + a) ^ 2 ), sq_nonneg ( (c + a) ^ 2 - (a + b) ^ 2 ), 
    sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (a - b - c), 
    sq_nonneg (a + b + c),
    sq_nonneg ((a + b) - (b + c)), sq_nonneg ((b + c) - (c + a)), sq_nonneg ((c + a) - (a + b)), 
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a) ]