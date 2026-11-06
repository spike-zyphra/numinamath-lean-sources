import Mathlib

theorem inequalities_601447 (a b c : ℝ) :
    (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b + b * c + c * a - 1)^2 := by
  nlinarith [sq_nonneg (a * b * c), sq_nonneg (a + b + c - a * b * c), 
          sq_nonneg (a * b + b * c + c * a), sq_nonneg (a * b * c - 1), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c), sq_nonneg (a * b * c - 1),
          sq_nonneg (a * b * c + 1), 
          mul_nonneg (show (0 : ℝ) ≤ a^2 by nlinarith [sq_nonneg a]) 
          (show (0 : ℝ) ≤ b^2 by nlinarith [sq_nonneg b]), 
          mul_nonneg (show (0 : ℝ) ≤ b^2 by nlinarith [sq_nonneg b]) 
          (show (0 : ℝ) ≤ c^2 by nlinarith [sq_nonneg c]), 
          mul_nonneg (show (0 : ℝ) ≤ a^2 by nlinarith [sq_nonneg a]) 
          (show (0 : ℝ) ≤ c^2 by nlinarith [sq_nonneg c])
        ]