import Mathlib

theorem algebra_16119 (x : Fin 3 → ℝ) (hx : 0 ≤ x 3 ∧ x 3 ≤ x 2 ∧ x 2 ≤ x 1 ∧ x 1 ≤ 1)
    (h : (1 - x 1)^2 + (x 1 - x 2)^2 + (x 2 - x 3)^2 + x 3^2 = 1 / 4) :
    x 1 = 3 / 4 := by
  rcases hx with ⟨hx3, hx32, hx21, hx1⟩
  have h1 : x 1 = 3 / 4 := by
    nlinarith [sq_nonneg (1 - x 1 - 1 / 4), sq_nonneg (x 1 - x 2 - 1 / 4), sq_nonneg (x 2 - x 3 - 1 / 4), sq_nonneg (x 3 - 1 / 4),
      mul_nonneg (show 0 ≤ x 3 by linarith) (show 0 ≤ x 2 - x 3 by linarith),
      mul_nonneg (show 0 ≤ x 2 - x 3 by linarith) (show 0 ≤ x 1 - x 2 by linarith),
      mul_nonneg (show 0 ≤ x 1 - x 2 by linarith) (show 0 ≤ 1 - x 1 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ x 3 by linarith) (show (0 : ℝ) ≤ x 2 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ x 2 by linarith) (show (0 : ℝ) ≤ x 1 by linarith)
    ]
  exact h1