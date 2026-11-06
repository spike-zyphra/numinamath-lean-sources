import Mathlib
open Real

theorem inequalities_607832 (x y z : ℝ) (h₀ : 0 < x) (h₁ : 0 < y) (h₂ : 0 < z) :
(x + y + z)^2 * (y * z + z * x + x * y)^2 ≤ 3 * (y^2 + y * z + z^2) *
(z^2 + z * x + x^2) * (x^2 + x * y + y^2) := by 
  have h3 : 0 < x * y := by nlinarith
  have h4 : 0 < y * z := by nlinarith
  have h5 : 0 < z * x := by nlinarith
  have h9 : (x + y + z) ^ 2 * (y * z + z * x + x * y) ^ 2 ≤ 3 * ((y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) * (x ^ 2 + x * y + y ^ 2)) := by 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), 
      sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
        sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x * y - y * z),
          mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₂ h₀, 
            mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
              mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
                mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)
                ]
  linarith [h9]