import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197421 :
  IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
    a ∈ Icc (-7.5) 7.5 ∧ b ∈ Icc (-7.5) 7.5 ∧ c ∈ Icc (-7.5) 7.5 ∧ d ∈ Icc (-7.5) 7.5} 240 := by
  constructor
  · -- First part, show 240 is in the set
    use -7.5, 7.5, -7.5, 7.5
    norm_num [mem_Icc]
    all_goals norm_num
    all_goals try { linarith }
  · -- Second part, show it's the greatest element
    intro x hx
    rcases hx with ⟨a, b, c, d, heq, ha, hb, hc, hd⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    -- Now need to prove that given these constraints, the expression is ≤ 240
    nlinarith [sq_nonneg (a + 7.5), sq_nonneg (b - 7.5), sq_nonneg (c + 7.5), sq_nonneg (d - 7.5),
          sq_nonneg (a - 7.5), sq_nonneg (b + 7.5), sq_nonneg (c - 7.5), sq_nonneg (d + 7.5),
          mul_nonneg (show (0 : ℝ) ≤ 7.5 - a by linarith) (show (0 : ℝ) ≤ a + 7.5 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 7.5 - b by linarith) (show (0 : ℝ) ≤ b + 7.5 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 7.5 - c by linarith) (show (0 : ℝ) ≤ c + 7.5 by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 7.5 - d by linarith) (show (0 : ℝ) ≤ d + 7.5 by linarith)]