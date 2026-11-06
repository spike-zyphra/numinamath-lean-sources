import Mathlib

theorem inequalities_120961 (p q : ℝ) (x y z : ℝ)
    (h₀ : y = x^2 + p * x + q)
    (h₁ : z = y^2 + p * y + q)
    (h₂ : x = z^2 + p * z + q) :
    x^2 * y + y^2 * z + z^2 * x ≥ x^2 * z + y^2 * x + z^2 * y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + p), sq_nonneg (y + z + p), sq_nonneg (z + x + p), 
    mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - z)), 
    mul_nonneg (sq_nonneg (y - z)) (sq_nonneg (z - x)), 
    mul_nonneg (sq_nonneg (x - y)) (sq_nonneg (z - x)), 
    sq_nonneg ((x - y) * (x + y + p)), 
    sq_nonneg ((y - z) * (y + z + p)), 
    sq_nonneg ((z - x) * (z + x + p)), 
    mul_nonneg (sq_nonneg (x + y + p)) (sq_nonneg (y + z + p)), 
    mul_nonneg (sq_nonneg (y + z + p)) (sq_nonneg (z + x + p)), 
    mul_nonneg (sq_nonneg (x + y + p)) (sq_nonneg (z + x + p)), 
    sq_nonneg (x - z), sq_nonneg (y - x), sq_nonneg (z - y)
  ]