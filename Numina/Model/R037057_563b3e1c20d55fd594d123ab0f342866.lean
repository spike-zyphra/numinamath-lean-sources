import Mathlib

theorem inequalities_601481 (a b c d e : ℝ)
    (h₀ : 0 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e)
    (h₁ : a + b + c + d + e = 1) :
    a * d + d * c + c * b + b * e + e * a ≤ 1 / 5 := by
  rcases h₀ with ⟨ha1, h2, h3, h4, h5⟩
  nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 1 / 5), sq_nonneg (c - 1 / 5), 
          sq_nonneg (d - 1 / 5), sq_nonneg (e - 1 / 5),
          h₁, mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b - a by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b - a by linarith) (show (0 : ℝ) ≤ c - b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ c - b by linarith) (show (0 : ℝ) ≤ d - c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ d - c by linarith) (show (0 : ℝ) ≤ e - d by linarith)
          ]