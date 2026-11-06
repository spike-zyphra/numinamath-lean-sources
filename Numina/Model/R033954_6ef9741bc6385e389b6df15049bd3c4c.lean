import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_321572 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 ∧ t = x^3 + 2*y^2 + 10/3*z} (10/3) ∧
  IsLeast {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 ∧ t = x^3 + 2*y^2 + 10/3*z} (14/27) := by
  constructor
  · -- Let's prove that 10/3 is the greatest element in the set.
    constructor
    · -- Show that 10/3 is achievable with x = 0, y = 0, z = 1.
      use 0, 0, 1
      norm_num
    · -- Show that 10/3 is an upper bound.
      intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, h_eq, ht⟩
      have h1 : z = 1 - x - y := by linarith
      rw [h1] at ht
      nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (x + y - 1),
        sq_nonneg (x - 0), sq_nonneg (y - 0),
        sq_nonneg (x - y), sq_nonneg (x + y - 1),
        mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ 1 - x - y by linarith [show x + y ≤ 1 by linarith]), mul_nonneg hy (show 0 ≤ 1 - x - y by linarith [show x + y ≤ 1 by linarith])]
  · -- Now, let's prove that 14/27 is the least element in the set.
    constructor
    · -- Show that 14/27 is achievable with x = 2/3, y = 1/3, z = 0.
      use 2/3, 1/3, 0
      norm_num
    · -- Show that 14/27 is a lower bound.
      intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, h_eq, ht⟩
      have h1 : z = 1 - x - y := by linarith
      rw [h1] at ht
      nlinarith [sq_nonneg (x - 2/3), sq_nonneg (y - 1/3), sq_nonneg (x + y - 1),
        sq_nonneg (x - 0), sq_nonneg (y - 0),
        sq_nonneg (x - y), sq_nonneg (x + y - 1),
        mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ 1 - x - y by linarith [show x + y ≤ 1 by linarith]), mul_nonneg hy (show 0 ≤ 1 - x - y by linarith [show x + y ≤ 1 by linarith])]