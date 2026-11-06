import Mathlib

theorem inequalities_218681 (x y z : ℝ) :
    (x^2 + y^2 + z^2) * ((x^2 + y^2 + z^2)^2 - (x * y + y * z + z * x)^2) ≥
    (x + y + z)^2 * ((x^2 + y^2 + z^2) - (x * y + y * z + z * x))^2 := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
        sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
        sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
        sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
        sq_nonneg (x + y + z), 
        sq_nonneg ((x - y) + (y - z) + (z - x)), 
        mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z)), 
        mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (z - x)), 
        mul_nonneg (sq_nonneg (y - z)) (sq_nonneg (z - x)), 
        sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x)
        ]