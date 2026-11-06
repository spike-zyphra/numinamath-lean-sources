import Mathlib

theorem inequalities_173510 (a b c : ℝ) : (a * b + b * c + c * a - 1) ^ 2 ≤
    (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := by
  nlinarith [sq_nonneg (a * b * c - (a + b + c)), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (a * b + b * c + c * a - a * b * c), sq_nonneg (a + b + c - a * b * c),
            sq_nonneg (a * b * c - (a + b + c)), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - c)), 
            mul_nonneg (sq_nonneg (a - c)) (sq_nonneg (b - c)), 
            mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)), 
            mul_nonneg (sq_nonneg (a)) (sq_nonneg (b)), 
            mul_nonneg (sq_nonneg (b)) (sq_nonneg (c)), 
            mul_nonneg (sq_nonneg (a)) (sq_nonneg (c))]