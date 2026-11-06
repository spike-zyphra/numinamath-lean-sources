import Mathlib

theorem inequalities_29949 (a x y z : ℝ) (ha : a = x + y + z) :
    (a - x)^4 + (a - y)^4 + (a - z)^4 +
    2 * (x^3 * y + y^3 * x + z^3 * x + x^3 * z + y^3 * z + z^3 * y) +
    4 * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) +
    8 * x * y * z * a ≥
    (a - x)^2 * (a^2 - x^2) + (a - y)^2 * (a^2 - y^2) + (a - z)^2 * (a^2 - z^2) := by 
  rw [ha]
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
            sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
            sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
            sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
            sq_nonneg (x - y + z), sq_nonneg (x + y - z), sq_nonneg (x - y + z),
            mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z)), mul_nonneg (sq_nonneg (y - z)) (sq_nonneg (z - x)), mul_nonneg (sq_nonneg (z - x)) (sq_nonneg (x - y)), 
            mul_nonneg (sq_nonneg (x * y - y * z)) (sq_nonneg (y * z - z * x)), mul_nonneg (sq_nonneg (y * z - z * x)) (sq_nonneg (z * x - x * y)), mul_nonneg (sq_nonneg (z * x - x * y)) (sq_nonneg (x * y - y * z)), 
            sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
            sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
            sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y))]