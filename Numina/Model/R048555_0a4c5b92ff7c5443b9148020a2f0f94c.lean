import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_325102 :
  IsLeast {x | ∃ a b : ℝ, x = a^2 + a * b + b^2 - a - b} (-1 / 3) := by
  constructor
  · -- Show that -1/3 is in the set
    use 1 / 3, 1 / 3
    norm_num
  · -- Show that -1/3 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, rfl⟩
    nlinarith [sq_nonneg (a + (b - 1) / 2), sq_nonneg (b - 1 / 3), sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3)]