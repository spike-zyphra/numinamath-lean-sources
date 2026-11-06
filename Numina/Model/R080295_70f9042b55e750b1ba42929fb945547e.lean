import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_212882 :
  IsLeast {n : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z * (x + y + z) = 1 ∧ n = (x + y) * (y + z)} 2 := by
  constructor
  · -- Show 2 is in the set
    use 1, Real.sqrt 2 - 1, 1
    have h1 : Real.sqrt 2 > 0 := by positivity
    have h2 : Real.sqrt 2 - 1 > 0 := by
      have hsqrt2 : Real.sqrt 2 > 1 := by
        have h : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
        linarith
      nlinarith
    have h3 : Real.sqrt 2 ^ 2 = 2 := by
      exact Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    constructor
    · -- Show x > 0
      norm_num
    constructor
    · -- Show y > 0
      linarith [h2]
    constructor
    · -- Show z > 0
      norm_num
    constructor
    · -- Show constraint
      nlinarith [h3, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
    · -- Show (x + y) * (y + z) = 2
      nlinarith [h3, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
  · -- Show 2 is a lower bound
    intro n hn
    rcases hn with ⟨x, y, z, hx, hy, hz, h1, heq⟩
    have h2 : (x + y) * (y + z) ≥ 2 := by
      nlinarith [sq_nonneg (x * z - 1), sq_nonneg (y - 1), sq_nonneg (x * y - 1), sq_nonneg (z * y - 1), sq_nonneg (x - z), sq_nonneg (x * y * z - 1 / (x + y + z)), mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
    nlinarith