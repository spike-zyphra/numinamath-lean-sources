import Mathlib

theorem inequalities_71105 (a b c : ℝ) (ha : a ∈ Set.Icc (-1) 1) (hb : b ∈ Set.Icc (-1) 1)
    (hc : c ∈ Set.Icc (-1) 1) (h : 1 + 2 * a * b * c ≥ a ^ 2 + b ^ 2 + c ^ 2) :
    1 + 2 * a ^ 2 * b ^ 2 * c ^ 2 ≥ a ^ 4 + b ^ 4 + c ^ 4 := by 
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - c), sq_nonneg (a * c - b), sq_nonneg (b * c - a),
          mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ a + 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - b by linarith) (show (0 : ℝ) ≤ b + 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - c by linarith) (show (0 : ℝ) ≤ c + 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 - b by linarith) (show (0 : ℝ) ≤ 1 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a + 1 by linarith) (show (0 : ℝ) ≤ b + 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a + 1 by linarith) (show (0 : ℝ) ≤ c + 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b + 1 by linarith) (show (0 : ℝ) ≤ c + 1 by linarith)
        ]