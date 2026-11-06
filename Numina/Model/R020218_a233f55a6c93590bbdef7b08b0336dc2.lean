import Mathlib

theorem inequalities_602113 (a b c d p q : ℝ) (h₀ : a * b + c * d = 2 * p * q)
    (h₁ : a * c ≥ p ^ 2) (h₂ : p ^ 2 > 0) : b * d ≤ q ^ 2 := by

  nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (p - q),
          sq_nonneg (a * b - c * d), sq_nonneg (a * d - b * c), sq_nonneg (a * c - p ^ 2), sq_nonneg (b + d - 2 * q),
          mul_pos (show 0 < p ^ 2 by linarith) (show 0 < p ^ 2 by linarith)
]