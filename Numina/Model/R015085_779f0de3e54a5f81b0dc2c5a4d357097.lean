import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_307347 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 ∧ t = (x + 3 * y + 5 * z) * (x + y / 3 + z / 5)} 1 ∧
  IsGreatest {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 1 ∧ t = (x + 3 * y + 5 * z) * (x + y / 3 + z / 5)} (9 / 5) := by

  constructor
  · -- Show that 1 is the least in the set.
    constructor
    · -- Show 1 is in the set.
      use 1, 0, 0
      norm_num
    · -- Show that 1 is a lower bound.
      intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y), sq_nonneg (z), 
        sq_nonneg (x + y + z - 1), 
        mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]
  · -- Show that 9/5 is the greatest in the set.
    constructor
    · -- Show 9/5 is in the set.
      use 1 / 2, 0, 1 / 2
      norm_num
    · -- Show that 9/5 is an upper bound.
      intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
      have h1' : z = 1 - x - y := by linarith
      rw [h1'] at ht
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 0), sq_nonneg ((1 - x - y) - 1 / 2), 
        mul_nonneg hx hy, mul_nonneg hx (show (1 - x - y) ≥ 0 by nlinarith), 
        mul_nonneg hy (show (1 - x - y) ≥ 0 by nlinarith)]