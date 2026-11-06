import Mathlib

theorem inequalities_601161 (x4 x3 x2 x1 y2 y1 : ℝ)
    (h₀ : y2 ≥ y1) (h₁ : y1 ≥ x4) (h₂ : x4 ≥ x3) (h₃ : x3 ≥ x2)
    (h₄ : x2 ≥ x1) (h₅ : x1 ≥ 2) (h₆ : x1 + x2 + x3 + x4 ≥ y1 + y2) :
    x1 * x2 * x3 * x4 ≥ y1 * y2 := by
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ x1 by linarith) (show (0 : ℝ) ≤ x2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x1 by linarith) (show (0 : ℝ) ≤ x3 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x1 by linarith) (show (0 : ℝ) ≤ x4 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x2 by linarith) (show (0 : ℝ) ≤ x3 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x2 by linarith) (show (0 : ℝ) ≤ x4 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x3 by linarith) (show (0 : ℝ) ≤ x4 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ y1 by linarith) (show (0 : ℝ) ≤ y2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x1 - 2 by linarith) (show (0 : ℝ) ≤ x2 - 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x1 - 2 by linarith) (show (0 : ℝ) ≤ x3 - 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x1 - 2 by linarith) (show (0 : ℝ) ≤ x4 - 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x2 - 2 by linarith) (show (0 : ℝ) ≤ x3 - 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x2 - 2 by linarith) (show (0 : ℝ) ≤ x4 - 2 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x3 - 2 by linarith) (show (0 : ℝ) ≤ x4 - 2 by linarith)
]