import Mathlib

theorem inequalities_605800
    (a b c d : ℝ)
    (ha : 0 ≤ a)
    (hb : a ≤ b)
    (hc : b ≤ c)
    (hd : c ≤ d) :
    a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2 ≤ a * b^3 + b * c^3 + c * d^3 + d * a^3 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a), 
          sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - d), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b - a by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c - b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ d - c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c - b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ d - c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ d - c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ d by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ a by linarith)
        ]