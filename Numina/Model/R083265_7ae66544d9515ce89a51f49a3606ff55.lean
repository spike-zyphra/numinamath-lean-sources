import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319184 :
  IsGreatest {p : ℝ | ∃ x y, p = x^2 - x * y + y^2 ∧ x^2 + x * y + y^2 = 3} 9 ∧
  IsLeast {p : ℝ | ∃ x y, p = x^2 - x * y + y^2 ∧ x^2 + x * y + y^2 = 3} 1 := by
  constructor
  · -- Show 9 is the greatest value in the set
    constructor
    · -- Show 9 is achievable by some x, y
      use Real.sqrt 3, -Real.sqrt 3
      constructor
      · -- Show that calculated value is 9
        nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) from by norm_num)]
      · -- Show constraint is met
        nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) from by norm_num)]
    · -- Show nothing greater than 9 is in the set
      intro p hp
      rcases hp with ⟨x, y, hp_eq, h_const⟩
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x)]
  · -- Show 1 is the least value in the set
    constructor
    · -- Show 1 is achievable by some x, y
      use (1 : ℝ), (1 : ℝ)
      constructor
      · -- Show the calculated value is 1
        norm_num
      · -- Show the constraint is met
        norm_num
    · -- Show nothing smaller than 1 is in the set
      intro p hp
      rcases hp with ⟨x, y, hp_eq, h_const⟩
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x)]