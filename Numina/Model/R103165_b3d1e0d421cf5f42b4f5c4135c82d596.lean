import Mathlib

theorem algebra_195238 :
    IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
      a ∈ Set.Icc (-8) 8 ∧ b ∈ Set.Icc (-8) 8 ∧ c ∈ Set.Icc (-8) 8 ∧ d ∈ Set.Icc (-8) 8} 272 := by
  constructor
  · -- First part: Show that 272 is attainable
    use -8, 8, -8, 8
    norm_num [Set.mem_Icc]
    all_goals linarith
  · -- Second part: Show that for all possible a,b,c,d, the expression is at most 272
    intro x hx
    rcases hx with ⟨a, b, c, d, heq, ha, hb, hc, hd⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    nlinarith [sq_nonneg (a + 8), sq_nonneg (b - 8), sq_nonneg (c + 8), sq_nonneg (d - 8),
      sq_nonneg (a - c), sq_nonneg (b - d),
      mul_nonneg (show (0 : ℝ) ≤ 16 - a by linarith) (show (0 : ℝ) ≤ 16 + a by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 16 - b by linarith) (show (0 : ℝ) ≤ 16 + b by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 16 - c by linarith) (show (0 : ℝ) ≤ 16 + c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 16 - d by linarith) (show (0 : ℝ) ≤ 16 + d by linarith)
    ]