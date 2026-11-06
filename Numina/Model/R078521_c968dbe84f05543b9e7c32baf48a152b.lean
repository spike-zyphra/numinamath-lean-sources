import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_315118 :
  IsLeast {x | ∃ a b c : ℝ, x = a^2 + 2*b^2 + 3*c^2 + 2*a*b + 4*b*c + 2*c*a - 6*a - 10*b - 12*c} (-14) := by
  constructor
  · -- Show -14 is in the set
    use 1, 1, 1
    norm_num
  · -- Show that -14 is the minimum
    intro x
    rintro ⟨a, b, c, heq⟩
    nlinarith [sq_nonneg (a + b + c - 3), sq_nonneg (b + c - 2), sq_nonneg (c - 1)]