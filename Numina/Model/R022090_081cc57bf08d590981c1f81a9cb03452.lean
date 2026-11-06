import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_288907 :
  IsGreatest {x | ∃ a b c : ℝ, x = a^2 + b^2 + c^2 ∧
    0 ≤ a + b ∧ a + b ≤ 1 ∧ 0 ≤ b + c ∧ b + c ≤ 1 ∧ 0 ≤ c + a ∧ c + a ≤ 1} 1 := by
  constructor
  · -- Show that 1 is in the set
    use 0, 0, 1
    norm_num
  · -- Show that 1 is the greatest
    intro x hx
    rcases hx with ⟨a, b, c, h_eq, h1, h2, h3, h4, h5, h6⟩
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]