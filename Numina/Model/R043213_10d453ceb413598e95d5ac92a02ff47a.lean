import Mathlib

theorem inequalities_36625 (a b c d : ℝ) (h₀ : a ≥ b) (h₁ : c ≥ d) :
    ∃ x : ℝ, (x + a) * (x + d) + (x + b) * (x + c) = 0 := by
  have h2 : (a + b + c + d) ^ 2 ≥ 8 * (a * d + b * c) := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - c - d), 
        sq_nonneg (a - c + b - d), sq_nonneg (a - b + c - d), 
          mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ c - d by linarith), 
            mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ c - d by linarith), 
              sq_nonneg (a - c), sq_nonneg (b - d)
          ]
  use (- (a + b + c + d) + Real.sqrt ((a + b + c + d) ^ 2 - 8 * (a * d + b * c)) ) / (4 : ℝ)
  nlinarith [ Real.sqrt_nonneg ((a + b + c + d) ^ 2 - 8 * (a * d + b * c)), 
          Real.sq_sqrt (show (a + b + c + d) ^ 2 - 8 * (a * d + b * c) ≥ 0 by 
            nlinarith [h2]
          )
  ]