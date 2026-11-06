import Mathlib

theorem algebra_195475 :
    IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
      a ∈ Set.Icc (-5) 5 ∧ b ∈ Set.Icc (-5) 5 ∧ c ∈ Set.Icc (-5) 5 ∧ d ∈ Set.Icc (-5) 5} 110 := by
  constructor
  · -- Show that 110 is achievable
    use -5, 5, -5, 5
    norm_num [Set.mem_Icc]
  · -- Show that 110 is indeed the greatest
    rintro x ⟨a, b, c, d, hx, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩, ⟨hd1, hd2⟩⟩
    have h1 : a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ≤ 110 := by
      nlinarith [sq_nonneg (a + 5), sq_nonneg (b - 5), sq_nonneg (c + 5), sq_nonneg (d - 5),
          sq_nonneg (a + c + 10), sq_nonneg (b + d - 10),
          mul_nonneg (show (0 : ℝ) ≤ 5 + a by linarith) (show (0 : ℝ) ≤ 5 - a by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 5 + b by linarith) (show (0 : ℝ) ≤ 5 - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 5 + c by linarith) (show (0 : ℝ) ≤ 5 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 5 + d by linarith) (show (0 : ℝ) ≤ 5 - d by linarith)
        ]
    linarith [h1, hx]