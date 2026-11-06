import Mathlib

open Real
open scoped BigOperators

theorem inequalities_221142
  (x y z : ℝ)
  (h₀ : 0 < x)
  (h₁ : 0 < y)
  (h₂ : 0 < z) :
  x^4 * y^2 * z + y^4 * x^2 * z + y^4 * z^2 * x + z^4 * y^2 * x + x^4 * z^2 * y + z^4 * x^2 * y ≥
  2 * (x^3 * y^2 * z^2 + x^2 * y^3 * z^2 + x^2 * y^2 * z^3) := by
  nlinarith [sq_nonneg (x * y - x * z), sq_nonneg (x * y - y * z), sq_nonneg (x * z - y * z), 
          sq_nonneg (x ^ 2 * y - x ^ 2 * z), sq_nonneg (x ^ 2 * y - y ^ 2 * z), sq_nonneg (x ^ 2 * z - y ^ 2 * z), 
          sq_nonneg (y ^ 2 * x - y ^ 2 * z), sq_nonneg (z ^ 2 * x - z ^ 2 * y), sq_nonneg (x * y ^ 2 - x * z ^ 2), 
          mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
          sq_nonneg (x ^ 2 * (y - z) ), sq_nonneg (y ^ 2 * (x - z) ), sq_nonneg (z ^ 2 * (y - x) ), 
          sq_nonneg (x * y * (y - z) ), sq_nonneg (x * z * (x - y) ), sq_nonneg (y * z * (y - x) ), 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < x * z by nlinarith), 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
          mul_pos (show 0 < x * z by nlinarith) (show 0 < y * z by nlinarith)
]