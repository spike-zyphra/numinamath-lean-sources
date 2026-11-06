import Mathlib

open Real Set

theorem algebra_327856 :
    IsGreatest {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 2 ∧ t = x^2 * y^2 + y^2 * z^2 + z^2 * x^2} 1 ∧
    IsLeast {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + y + z = 2 ∧ t = x^2 * y^2 + y^2 * z^2 + z^2 * x^2} 0 := by
  constructor
  · -- Show 1 is the greatest value in the set
    constructor
    · -- Show 1 exists in the set
      use 1, 1, 0
      norm_num
    · -- Show no value greater than 1 is in the set
      intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
      -- We need to show that $t \leq 1$ for any point (x, y, z) in the set.
      have h2 : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 ≤ 1 := by
        have h3 : z = 2 - x - y := by linarith
        rw [h3]
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - (2 - x - y)), sq_nonneg (x - (2 - x - y)), 
          sq_nonneg (x + y - 1), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg ((2 - x - y) - 1),
          mul_nonneg hx hy, mul_nonneg hx (show (2 - x - y) ≥ 0 by nlinarith), mul_nonneg hy (show (2 - x - y) ≥ 0 by nlinarith)]
      linarith [ht, h2]
  · -- Show 0 is the least value in the set
    constructor
    · -- Show 0 exists in the set
      use 2, 0, 0
      norm_num
    · -- Show no value less than 0 is in the set
      intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩
      -- The value in the set is the sum of non-negative terms, so it's non-negative.
      have h2 : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 ≥ 0 := by
        positivity
      linarith [ht, h2]