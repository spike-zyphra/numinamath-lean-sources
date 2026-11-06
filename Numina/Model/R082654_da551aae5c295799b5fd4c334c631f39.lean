import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_132222 :
  IsGreatest {x | ∃ a b c d : ℝ, x = a + b + c + d - a * b - b * c - c * d - d * a ∧
    0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ 0 ≤ c ∧ c ≤ 1 ∧ 0 ≤ d ∧ d ≤ 1} 2 := by 
  constructor
  · -- Show 2 is in the set
    use 1, 0, 1, 0
    norm_num
  · -- Show that for any expression in the set, its value ≤ 2
    intro x h
    rcases h with ⟨a, b, c, d, h_eq, ha1, ha2, hb1, hb2, hc1, hc2, hd1, hd2⟩
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1),
      sq_nonneg (a - c), sq_nonneg (b - d)]