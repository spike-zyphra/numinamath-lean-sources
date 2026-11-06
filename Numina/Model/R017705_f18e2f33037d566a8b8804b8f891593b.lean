import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13978 : IsLeast {x | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
  a^2 + b^2 + c^2 + a + 2*b + 3*c = 13/4 ∧ x = a + b + c} ((-3 + sqrt 22) / 2) := by 
  constructor
  · -- We need to prove ` (-3 + sqrt 22) / 2` is in the set.
    use 0, 0, (-3 + Real.sqrt 22) / 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show that c ≥ 0
      have h1 : (-3 + Real.sqrt 22) / 2 ≥ 0 := by
        have h2 : Real.sqrt 22 ≥ 3 := by
          nlinarith [Real.sqrt_nonneg (22 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (22 : ℝ) by norm_num), sq_nonneg (Real.sqrt 22 - 3)]
        nlinarith
      linarith
    constructor
    · -- Verify the equation
      nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show (0 : ℝ) ≤ (22 : ℝ) by norm_num) ]
    · -- Verify the sum equals to the claimed minimum
      all_goals
        ring
  · -- We need to prove the minimum
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, heq, hx⟩
    nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), sq_nonneg (c - (-3 + Real.sqrt 22) / 2), 
              sq_nonneg (a^2 + b^2 + c^2 - 13 / 4), 
              Real.sqrt_nonneg 22, 
              Real.sq_sqrt (show (0 : ℝ) ≤ (22 : ℝ) by norm_num), 
              mul_nonneg ha hb, 
              mul_nonneg hb hc, 
              mul_nonneg ha hc
    ]