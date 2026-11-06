import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_270283 :
  IsLeast {x | ∃ a b : ℝ, x = a^2 + 6*b^2 - 2*a*b - 14*a - 6*b + 72} 3 := by
  constructor
  · use 9, 2
    norm_num
  · intro x hx
    rcases hx with ⟨a, b, hx⟩
    nlinarith [sq_nonneg (a - 9), sq_nonneg (b - 2), sq_nonneg (a - 2*b - 5), sq_nonneg (2*a - 3*b - 12), sq_nonneg (a - 9), sq_nonneg (b - 2)]