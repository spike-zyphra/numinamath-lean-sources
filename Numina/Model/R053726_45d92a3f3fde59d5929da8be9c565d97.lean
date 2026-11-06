import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_198115 :
  IsLeast {t : ℝ | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ t = x^3 + y^3 - 5 * x * y} (-125/27) := by
  constructor
  · -- Show that -125/27 is in the set
    use 5 / 3, 5 / 3
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that -125/27 is a lower bound
    intro t ht
    rcases ht with ⟨x, y, hx, hy, h_eq⟩
    have h : x^3 + y^3 - 5 * x * y ≥ -125/27 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 5 / 3), sq_nonneg (y - 5 / 3),
        sq_nonneg (x + y - 10 / 3), sq_nonneg (x * y - (5 / 3)^2),
        mul_nonneg hx hy, sq_nonneg (x^2 - (5 / 3)^2), sq_nonneg (y^2 - (5 / 3)^2)]
    linarith [h_eq, h]