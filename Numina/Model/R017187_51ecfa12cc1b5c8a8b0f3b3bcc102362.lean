import Mathlib

theorem inequalities_90007 (a b c : ℝ) (h₀ : 0 ≤ c) (h₁ : c ≤ b) (h₂ : b ≤ a) :
    a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - c), sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), 
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ b - c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b - c by linarith) (show (0 : ℝ) ≤ a - b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ a - b by linarith)]