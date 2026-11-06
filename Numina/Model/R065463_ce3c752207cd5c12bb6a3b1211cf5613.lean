import Mathlib

theorem inequalities_305650 (a b c d e : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b) (h₂ : b ≤ c)
    (h₃ : c ≤ d) (h₄ : d ≤ e) (h₅ : a + b + c + d + e = 1) :
    a * d + d * c + c * b + b * e + e * a ≤ 1 / 5 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - e),
          sq_nonneg (a - 1 / 5), sq_nonneg (b - 1 / 5), sq_nonneg (c - 1 / 5), sq_nonneg (d - 1 / 5), sq_nonneg (e - 1 / 5),
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b - a by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ d - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ d by linarith) (show (0 : ℝ) ≤ e - d by linarith)]