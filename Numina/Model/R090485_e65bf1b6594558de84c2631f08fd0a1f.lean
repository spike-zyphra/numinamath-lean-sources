import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197827 :
  IsGreatest {x | ∃ a b c d : ℝ, a ∈ Icc (-12.5) 12.5 ∧ b ∈ Icc (-12.5) 12.5 ∧
    c ∈ Icc (-12.5) 12.5 ∧ d ∈ Icc (-12.5) 12.5 ∧ x = a + 2*b + c + 2*d - a*b - b*c - c*d - d*a} 650 := by 
  constructor
  · -- Show that 650 is achievable
    use -12.5, 12.5, -12.5, 12.5
    constructor
    · -- Show a ∈ Icc (-12.5) 12.5
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show b ∈ Icc (-12.5) 12.5
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show c ∈ Icc (-12.5) 12.5
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show d ∈ Icc (-12.5) 12.5
      exact ⟨by norm_num, by norm_num⟩
    · -- Show the value equals 650
      norm_num
  · -- Show that 650 is the maximum
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, h_eq⟩
    rw [h_eq]
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    nlinarith [sq_nonneg (a + 12.5), sq_nonneg (c + 12.5),
      sq_nonneg (b - 12.5), sq_nonneg (d - 12.5),
      mul_nonneg (show (0 : ℝ) ≤ 12.5 - a by linarith) (show (0 : ℝ) ≤ a + 12.5 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 12.5 - b by linarith) (show (0 : ℝ) ≤ b + 12.5 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 12.5 - c by linarith) (show (0 : ℝ) ≤ c + 12.5 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 12.5 - d by linarith) (show (0 : ℝ) ≤ d + 12.5 by linarith)]