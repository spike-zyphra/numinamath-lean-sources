import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_280405 :
  IsGreatest {x | ∃ a b c d : ℝ, a^2 + b^2 + c^2 + d^2 ≤ 1 ∧
    x = (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4} 6 := by
  constructor
  · -- Show 6 is in the set
    use 1 / 2, 1 / 2, 1 / 2, 1 / 2 
    constructor
    · norm_num 
    · norm_num 
  · -- Show that 6 is the greatest element in the set 
    intro x hx 
    rcases hx with ⟨a, b, c, d, h1, hx⟩
    have h2 : (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ≤ 6 := by 
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (a^2 - d^2), sq_nonneg (b^2 - c^2), sq_nonneg (b^2 - d^2), sq_nonneg (c^2 - d^2), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a + b + c + d), sq_nonneg (a - b + c - d), sq_nonneg (a + b - c - d), sq_nonneg (-a + b + c - d)]
    linarith [hx, h2]