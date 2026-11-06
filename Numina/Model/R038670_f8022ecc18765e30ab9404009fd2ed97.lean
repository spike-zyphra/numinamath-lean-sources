import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197668 :
  IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
    a ∈ Icc (-10.5) 10.5 ∧ b ∈ Icc (-10.5) 10.5 ∧ c ∈ Icc (-10.5) 10.5 ∧ d ∈ Icc (-10.5) 10.5} 462 := by
  constructor
  · -- Show that 462 belongs to the set
    use -10.5, 10.5, -10.5, 10.5
    constructor
    · -- Verify that the expression evaluates to 462
      norm_num
    constructor
    · -- Show that -10.5 ∈ [-10.5, 10.5]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that 10.5 ∈ [-10.5, 10.5]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that -10.5 ∈ [-10.5, 10.5]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that 10.5 ∈ [-10.5, 10.5]
      exact ⟨by norm_num, by norm_num⟩
  · -- Show that 462 is greatest
    intro x hx
    rcases hx with ⟨a, b, c, d, hx1, ha, hb, hc, hd⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    nlinarith [sq_nonneg (a + 10.5), sq_nonneg (b - 10.5), sq_nonneg (c + 10.5), sq_nonneg (d - 10.5),
          mul_nonneg (show (0 : ℝ) ≤ 10.5 + a by linarith) (show (0 : ℝ) ≤ 10.5 - a by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 10.5 + b by linarith) (show (0 : ℝ) ≤ 10.5 - b by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 10.5 + c by linarith) (show (0 : ℝ) ≤ 10.5 - c by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 10.5 + d by linarith) (show (0 : ℝ) ≤ 10.5 - d by linarith)]