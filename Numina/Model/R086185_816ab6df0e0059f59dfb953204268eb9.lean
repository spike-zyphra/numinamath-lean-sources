import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9704 :
  IsLeast {x | ∃ t : ℝ, x = t^4 + 4 * t^3 + 7 * t^2 + 6 * t + 2023} 2021 := by 
  constructor
  · -- First, prove that 2021 is attainable, i.e., there exists some t such that f(t) = 2021.
    use -1
    norm_num 
  · -- Now, prove that 2021 is a lower bound.
    intro y hy
    rcases hy with ⟨t, ht⟩
    have h : t^4 + 4 * t^3 + 7 * t^2 + 6 * t + 2023 ≥ 2021 := by 
      nlinarith [sq_nonneg (t^2 + 2 * t + 1), sq_nonneg (t + 1), sq_nonneg (t^2 + 2 * t + 1)]
    linarith