import Mathlib

theorem inequalities_598989 (a b c : ℝ) (ha : a ∈ Set.Icc 1 2) (hb : b ∈ Set.Icc 1 2) (hc : c ∈ Set.Icc 1 2)
    (hd : 0 < a) (he : 0 < b) (hf : 0 < c) :
    a^3 + b^3 + c^3 ≤ 5 * a * b * c := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ b - 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ c - 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b - 1 by linarith) (show (0 : ℝ) ≤ c - 1 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 2 - a by linarith) (show (0 : ℝ) ≤ 2 - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 2 - a by linarith) (show (0 : ℝ) ≤ 2 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 2 - b by linarith) (show (0 : ℝ) ≤ 2 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ 2 - a by linarith),
          mul_nonneg (show (0 : ℝ) ≤ b - 1 by linarith) (show (0 : ℝ) ≤ 2 - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ c - 1 by linarith) (show (0 : ℝ) ≤ 2 - c by linarith),
          mul_pos hd he, mul_pos hd hf, mul_pos he hf
]