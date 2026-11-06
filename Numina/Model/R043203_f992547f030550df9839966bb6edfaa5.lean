import Mathlib

theorem inequalities_111942 {x y z : ℝ} (h₁ : 2 * x > y ^ 2 + z ^ 2) (h₂ : 2 * y > x ^ 2 + z ^ 2)
    (h₃ : 2 * z > y ^ 2 + x ^ 2) : x * y * z < 1 := by 
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos (show (0 : ℝ) < 2 * x - y^2 - z^2 by linarith) (show (0 : ℝ) < 2 * y - x^2 - z^2 by linarith),
          mul_pos (show (0 : ℝ) < 2 * x - y^2 - z^2 by linarith) (show (0 : ℝ) < 2 * z - y^2 - x^2 by linarith),
          mul_pos (show (0 : ℝ) < 2 * y - x^2 - z^2 by linarith) (show (0 : ℝ) < 2 * z - y^2 - x^2 by linarith)
        ]