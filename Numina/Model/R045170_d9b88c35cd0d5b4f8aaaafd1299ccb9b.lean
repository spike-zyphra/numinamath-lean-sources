import Mathlib

theorem inequalities_603681 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ((2 * x + y) / 3 * (x + 2 * y) / 3) ^ 2 ≥ √(x * y) * ((x + y) / 2) ^ 3 := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h3 : (√(x * y)) ^ 2 = x * y := by
    rw [Real.sq_sqrt]
    positivity
  nlinarith [sq_nonneg ((2 * x + y) / 3 - (x + 2 * y) / 3), sq_nonneg (x - y),
            sq_nonneg (x * y - ((x + y) / 2) * (x + y) / 2),
            sq_nonneg ((2 * x + y) * (x + 2 * y) - 3 * ((x + y) / 2) ^ 2),
            sq_nonneg (√(x * y) - (x + y) / 2),
            Real.sqrt_nonneg (x * y), Real.sq_sqrt (show (0 : ℝ) ≤ x * y by positivity),
            sq_nonneg (x * y - (x * y)), mul_pos hx hy, sq_nonneg ((2 * x + y) * (x + 2 * y) - 3 * (x * y)), 
            pow_two_nonneg (x - y), 
            sq_nonneg (x * (x - y)), sq_nonneg (y * (y - x)),
            mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg (x * y))]