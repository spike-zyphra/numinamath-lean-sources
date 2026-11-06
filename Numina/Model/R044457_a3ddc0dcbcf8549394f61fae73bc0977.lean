import Mathlib

theorem algebra_21038 :
    IsGreatest {r : ℝ | ∃ x y : ℝ, 3 * x ^ 2 - 18 * x + 4 * y ^ 2 - 32 * y + 91 = 300 ∧ r = x ^ 2 + y ^ 2 + 2 * x * y - 14 * x - 14 * y + 49} 175 := by
  constructor
  · -- First part: proving 175 is in the set.
    use 3 + (20 * Real.sqrt 7 / 7), 4 + (15 * Real.sqrt 7 / 7)
    constructor
    · -- Verify the constraint equation
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
    · -- Verify r = ...
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]
  · -- Second part: proving 175 is greatest
    intro r h
    rcases h with ⟨x, y, h_eq, hr⟩
    nlinarith [sq_nonneg (x - (3 + (20 * Real.sqrt 7 / 7))), sq_nonneg (y - (4 + (15 * Real.sqrt 7 / 7))), 
          sq_nonneg (x - (3 - (20 * Real.sqrt 7 / 7))), sq_nonneg (y - (4 - (15 * Real.sqrt 7 / 7))), 
          sq_nonneg (x - 3 - 4 * (y - 4) / 3), sq_nonneg ((y - 4) + 3 * (x - 3) / 4),
          sq_nonneg (x + y - 7 - 5 * Real.sqrt 7), sq_nonneg (x + y - 7 + 5 * Real.sqrt 7),
          sq_nonneg (3 * (x - 3) - 4 * (y - 4)), sq_nonneg (x - 3 - 4 * Real.sqrt 7 / 7 * (5 : ℝ) / 5),
          Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)]