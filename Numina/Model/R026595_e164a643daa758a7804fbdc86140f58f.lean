import Mathlib

theorem algebra_197503 :
    IsGreatest {x | ∃ a b c d : ℝ, a ∈ Set.Icc (-8.5) 8.5 ∧ b ∈ Set.Icc (-8.5) 8.5 ∧
      c ∈ Set.Icc (-8.5) 8.5 ∧ d ∈ Set.Icc (-8.5) 8.5 ∧ x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a} 306 := by
  constructor
  · -- Show 306 is in the set
    use -8.5, 8.5, -8.5, 8.5
    norm_num [Set.mem_Icc]
  · -- Show that 306 is the greatest
    intro x h
    rcases h with ⟨a, b, c, d, ha, hb, hc, hd, hx⟩
    rw [hx]
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    nlinarith [sq_nonneg (a + 8.5), sq_nonneg (b - 8.5), sq_nonneg (c + 8.5), sq_nonneg (d - 8.5), 
        mul_nonneg (show (0 : ℝ) ≤ 8.5 + a by linarith) (show (0 : ℝ) ≤ 8.5 - a by linarith), 
        mul_nonneg (show (0 : ℝ) ≤ 8.5 + b by linarith) (show (0 : ℝ) ≤ 8.5 - b by linarith), 
        mul_nonneg (show (0 : ℝ) ≤ 8.5 + c by linarith) (show (0 : ℝ) ≤ 8.5 - c by linarith), 
        mul_nonneg (show (0 : ℝ) ≤ 8.5 + d by linarith) (show (0 : ℝ) ≤ 8.5 - d by linarith)
      ]