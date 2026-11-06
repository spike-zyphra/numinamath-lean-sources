import Mathlib

open Real

theorem algebra_305013 :
    IsLeast {x : ℝ | ∃ a b, x = a^2 + a * b + b^2 - a - b + 1 / 2} (1 / 6) := by
  constructor
  · -- Let's prove that 1/6 is in the set by showing that when a = b = 1/3, M = 1/6
    use 1 / 3, 1 / 3
    norm_num
  · -- Now, we need to prove that for any x in the set, 1/6 ≤ x
    intro x hx
    rcases hx with ⟨a, b, h_eq⟩
    -- Now x = a^2 + a * b + b^2 - a - b + 1 / 2 
    -- Let's show that 1/6 ≤ x
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (a - b), sq_nonneg (a + b - 2 / 3)]