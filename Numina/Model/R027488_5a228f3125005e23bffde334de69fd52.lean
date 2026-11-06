import Mathlib

theorem inequalities_7752 (a b c d : ℝ) (h₀ : 0 ≤ d) (h₁ : d ≤ c) (h₂ : c ≤ b) (h₃ : b ≤ a)
    (h₄ : a^2 + b^2 + c^2 + d^2 = 4) :
    a * b * c * d + (a - d)^2 ≥ 1 := by 
  have h6 : 0 ≤ c - d := by linarith
  have h7 : 0 ≤ b - c := by linarith
  have h8 : 0 ≤ a - b := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d),
          sq_nonneg (a - d), sq_nonneg (a^2 + b^2 + c^2 + d^2 - 4), 
          mul_nonneg (show (0:ℝ) ≤ b - c by linarith) (show (0:ℝ) ≤ c - d by linarith), 
          mul_nonneg (show (0:ℝ) ≤ d by linarith) (show (0:ℝ) ≤ c - d by linarith), 
          mul_nonneg (show (0:ℝ) ≤ a - b by linarith) (show (0:ℝ) ≤ b - c by linarith)]