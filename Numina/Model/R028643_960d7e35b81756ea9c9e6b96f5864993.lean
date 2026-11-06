import Mathlib

theorem inequalities_108842 (a b c d e : ℝ) (ha : 0 ≤ a) (h : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e)
    (h1 : a + b + c + d + e = 1) :
    a * d + d * c + c * b + b * e + e * a ≤ 1 / 5 := by
  rcases h with ⟨hab, hbc, hcd, hde⟩
  nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 1 / 5), sq_nonneg (c - 1 / 5), sq_nonneg (d - 1 / 5), sq_nonneg (e - 1 / 5),
          h1, mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - b by linarith),
          mul_nonneg (show 0 ≤ c - b by linarith) (show 0 ≤ d - c by linarith),
          mul_nonneg (show 0 ≤ d - c by linarith) (show 0 ≤ e - d by linarith),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b - a by linarith),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c - b by linarith),
          mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ c - b by linarith),
          mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ d - c by linarith),
          mul_nonneg (show 0 ≤ c - b by linarith) (show 0 ≤ e - d by linarith),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ e - d by linarith)
]