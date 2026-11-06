import Mathlib

theorem algebra_194988 :
    IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
      a ∈ Set.Icc (-6.5) 6.5 ∧ b ∈ Set.Icc (-6.5) 6.5 ∧ c ∈ Set.Icc (-6.5) 6.5 ∧ d ∈ Set.Icc (-6.5) 6.5} 182 := by
  constructor
  · -- Show 182 is in the set
    use -6.5, 6.5, -6.5, 6.5
    norm_num [Set.mem_Icc]

  · -- Show that 182 is greatest
    rintro x ⟨a, b, c, d, heq, ha, hb, hc, hd⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    nlinarith [sq_nonneg (a + 6.5), sq_nonneg (b - 6.5), sq_nonneg (c + 6.5), sq_nonneg (d - 6.5),
      sq_nonneg (a + c + 13), sq_nonneg (b + d - 13), sq_nonneg (a * b - 42.25), sq_nonneg (b * c - 42.25),
      mul_nonneg (show (0 : ℝ) ≤ 6.5 + 6.5 by norm_num) (show (0 : ℝ) ≤ 6.5 + 6.5 by norm_num),
      mul_nonneg (show (0 : ℝ) ≤ 6.5 + 6.5 by norm_num) (show (0 : ℝ) ≤ 6.5 + 6.5 by norm_num)]