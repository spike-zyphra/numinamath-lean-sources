import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11310 :
  IsLeast {z : ℝ | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z = x^3 + y^3 - 5 * x * y} (-125 / 27) := by
  constructor
  · -- First, we verify that -125/27 is indeed achievable with x = y = 5/3
    use 5 / 3, 5 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Now, we need to prove that for all z in the set, z ≥ -125/27
    intro z hz
    rcases hz with ⟨x, y, hx, hy, hz⟩
    have h1 : x ^ 3 + y ^ 3 - 5 * x * y ≥ -125 / 27 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 10 / 3), sq_nonneg (x - 5 / 3), sq_nonneg (y - 5 / 3),
        sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y - 25 / 9), sq_nonneg (x - y),
        sq_nonneg (x ^ 2 + y ^ 2 - 50 / 9), mul_nonneg hx hy,
        sq_nonneg (x + y - 10 / 3), sq_nonneg (x * (x - 5 / 3)), sq_nonneg (y * (y - 5 / 3)), 
        sq_nonneg (x - 5 / 3), sq_nonneg (y - 5 / 3)]
    linarith [hz, h1]