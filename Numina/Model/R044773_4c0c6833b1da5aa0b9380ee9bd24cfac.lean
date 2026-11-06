import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_165033 :
  IsGreatest {x : ℝ | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1 ∧ x = (a + 3*b + 5*c)*(a + b/3 + c/5)} (9/5) := by
  constructor
  · -- Show 9/5 is in the set
    use 1 / 2, (0 : ℝ), (1 / 2 : ℝ)
    constructor
    · norm_num  -- a ≥ 0
    constructor
    · norm_num  -- b ≥ 0
    constructor
    · norm_num  -- c ≥ 0
    constructor
    · norm_num -- a + b + c = 1
    norm_num
  · -- Show 9/5 is the greatest
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2⟩
    nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (c - 1 / 2), sq_nonneg (b), sq_nonneg (a - c), 
              mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc, 
              h1]