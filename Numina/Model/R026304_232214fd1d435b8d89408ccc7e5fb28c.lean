import Mathlib

theorem algebra_13175 (a b c : ℝ)
    (h₀ : 0 ≤ a + b ∧ a + b ≤ 1)
    (h₁ : 0 ≤ b + c ∧ b + c ≤ 1)
    (h₂ : 0 ≤ c + a ∧ c + a ≤ 1) :
    a ^ 2 + b ^ 2 + c ^ 2 ≤ 1 := by
  have h3 : a + b ≥ 0 := by linarith
  have h4 : a + b ≤ 1 := by linarith
  have h5 : b + c ≥ 0 := by linarith
  have h6 : b + c ≤ 1 := by linarith
  have h7 : c + a ≥ 0 := by linarith
  have h8 : c + a ≤ 1 := by linarith
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a + b + c - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_nonneg (show (0 : ℝ) ≤ 1 - (a + b) by linarith) (show (0 : ℝ) ≤ a + b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - (b + c) by linarith) (show (0 : ℝ) ≤ b + c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - (c + a) by linarith) (show (0 : ℝ) ≤ c + a by linarith)
        ]