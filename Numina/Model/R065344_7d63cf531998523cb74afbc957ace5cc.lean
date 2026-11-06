import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_315746 :
  IsGreatest {z : ℝ | ∃ x y, z = x^2 - x * y + y^2 ∧ x^2 + x * y + y^2 = 3} 9 ∧
  IsLeast {z : ℝ | ∃ x y, z = x^2 - x * y + y^2 ∧ x^2 + x * y + y^2 = 3} 1 := by
  constructor
  · -- We verify the greatest element is 9
    constructor
    · -- We need to show that 9 can be obtained
      use Real.sqrt 3, -Real.sqrt 3
      constructor
      · -- Show the value equals 9
        nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      · -- Verify the constraint
        nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- We need to show that 9 is the greatest possible value
      intro z hz
      rcases hz with ⟨x, y, h1, h2⟩
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
  · -- We verify the least element is 1
    constructor
    · -- We need to show that 1 can be obtained
      use (1 : ℝ), (1 : ℝ)
      norm_num
    · -- We need to show that 1 is the least possible value
      intro z hz
      rcases hz with ⟨x, y, h1, h2⟩
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]