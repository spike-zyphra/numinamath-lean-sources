import Mathlib

theorem inequalities_263663 (a b c d : ℝ) : (a^2 + b^2 + 1) * (c^2 + d^2 + 1) ≥ 2 * (a + c) * (b + d) := by
  have h1 : (a^2 + b^2 + 1) * (c^2 + d^2 + 1) - 2 * (a + c) * (b + d) ≥ 0 := by 
    nlinarith [sq_nonneg (a * c - b * d), sq_nonneg (a * d + b * c - (a * b + c * d)), 
            sq_nonneg (a + c - b - d), sq_nonneg (a - c - b + d), 
            sq_nonneg (a * c + b * d - 1), sq_nonneg (b * c - a * d), 
            sq_nonneg ((a * b + c * d) - (a * d + b * c)), 
            sq_nonneg ((a - b) * (c - d) - (a * c - b * d)), sq_nonneg (a * d - b * c), 
            sq_nonneg (a + b - c - d), sq_nonneg (a - b + c - d), sq_nonneg (a + c - (b + d)), sq_nonneg (a * b - c * d)
          ]
  linarith [h1]