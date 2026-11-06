import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_195073 :
  IsGreatest {x | ∃ a b c d : ℝ, a ∈ Icc (-7.5) 7.5 ∧ b ∈ Icc (-7.5) 7.5 ∧
    c ∈ Icc (-7.5) 7.5 ∧ d ∈ Icc (-7.5) 7.5 ∧ x = a + 2*b + c + 2*d - a*b - b*c - c*d - d*a} 240 := by

  constructor
  · -- Show that 240 is achievable with specific values
    use -7.5, 7.5, -7.5, 7.5
    norm_num [mem_Icc]
  · -- Show that no value greater than 240 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, h_eq⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    nlinarith [sq_nonneg (a + 7.5), sq_nonneg (a - 7.5), sq_nonneg (b + 7.5), sq_nonneg (b - 7.5),
      sq_nonneg (c + 7.5), sq_nonneg (c - 7.5), sq_nonneg (d + 7.5), sq_nonneg (d - 7.5),
      mul_nonneg (show 0 ≤ (15 : ℝ) by norm_num) (show 0 ≤ (15 : ℝ) by norm_num),
      mul_nonneg (show 0 ≤ (7.5 : ℝ) by norm_num) (show 0 ≤ (7.5 : ℝ) by norm_num)]