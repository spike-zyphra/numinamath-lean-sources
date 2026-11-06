import Mathlib

theorem algebra_601232 (a b c : ℝ) (h₀ : b + c > 0) (h₁ : c + a > 0) (h₂ : a + b > 0)
    (h₃ : a^2 + b^2 + c^2 + a * b * c = 4) : a + b + c > 2 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - 2), mul_pos (show (0 : ℝ) < b + c by linarith) (show (0 : ℝ) < c + a by linarith),
          mul_pos (show (0 : ℝ) < c + a by linarith) (show (0 : ℝ) < a + b by linarith),
          mul_pos (show (0 : ℝ) < a + b by linarith) (show (0 : ℝ) < b + c by linarith)]