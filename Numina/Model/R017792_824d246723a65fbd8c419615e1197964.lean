import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_321169 :
  IsLeast {x | ∃ a b : ℝ, x = a^4 + b^4 + 2*a^2*b - 2*a*b^2 + 3*a^2 + 3*b^2 - 2*a + 2*b + 2} (9/8) := by
  constructor
  · -- Show 9/8 is in the set
    use 1 / 2, -1 / 2
    norm_num
  · -- Show 9/8 is the least in the set
    intro x hx
    rcases hx with ⟨a, b, h⟩
    have h1 : a^4 + b^4 + 2*a^2*b - 2*a*b^2 + 3*a^2 + 3*b^2 - 2*a + 2*b + 2 - 9/8 ≥ 0 := by
      nlinarith [sq_nonneg (a - 1/2), sq_nonneg (b + 1/2), 
          sq_nonneg (a^2 - b), sq_nonneg (a - b - 1), sq_nonneg (a^2 - 1/4), sq_nonneg (b^2 - 1/4), sq_nonneg (a - 1/2), sq_nonneg (b + 1/2), 
          sq_nonneg (a^2 + b + 1/2), sq_nonneg (a - b), 
          sq_nonneg ((a - 1/2) * (b + 1/2)), 
          sq_nonneg ((a + 1/2) * (b - 1/2)), 
          sq_nonneg ((a - b) + 1), sq_nonneg ((a + b) + 0), 
          sq_nonneg (a^2 - b - 1/2), sq_nonneg (b^2 - (a - 1/2)^2 - 1/4)
        ]
    linarith [h, h1]