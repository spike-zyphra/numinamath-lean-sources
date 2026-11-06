import Mathlib

theorem algebra_197171 :
    IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
      a ∈ Set.Icc (-4.5) 4.5 ∧ b ∈ Set.Icc (-4.5) 4.5 ∧ c ∈ Set.Icc (-4.5) 4.5 ∧ d ∈ Set.Icc (-4.5) 4.5} 90 := by
  constructor
  · -- Show 90 is in the set
    use -4.5, 4.5, -4.5, 4.5
    norm_num [Set.mem_Icc]
  · -- Show any value in the set is ≤ 90
    intro x hx
    rcases hx with ⟨a, b, c, d, heq, ha, hb, hc, hd⟩

    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩

    nlinarith [sq_nonneg (a + 4.5), sq_nonneg (b - 4.5), sq_nonneg (c + 4.5), sq_nonneg (d - 4.5),
      sq_nonneg (a + c + 9), sq_nonneg (b + d - 9), sq_nonneg (a + c), sq_nonneg (b + d - 9),
      mul_nonneg (show (0 : ℝ) ≤ 4.5 - a by nlinarith) (show (0 : ℝ) ≤ 4.5 + a by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ 4.5 - b by nlinarith) (show (0 : ℝ) ≤ 4.5 + b by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ 4.5 - c by nlinarith) (show (0 : ℝ) ≤ 4.5 + c by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ 4.5 - d by nlinarith) (show (0 : ℝ) ≤ 4.5 + d by nlinarith)]