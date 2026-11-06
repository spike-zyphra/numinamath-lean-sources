import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_309052 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z * (x + y + z) = 1 ∧ t = (x + y) * (y + z)} 2 := by

  constructor
  · -- Show that 2 is in the set
    use 1, Real.sqrt 2 - 1, 1

    constructor
    · norm_num

    have h1 : 1 < Real.sqrt 2 := by
      rw [Real.lt_sqrt]
      all_goals norm_num

    have h2 : Real.sqrt 2 - 1 > 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), h1]

    constructor
    · -- Show that $y > 0$
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), h1]

    constructor
    · norm_num

    constructor
    · -- Show that $x * y * z * (x + y + z) = 1$
      have h5 : (1 : ℝ) * (Real.sqrt 2 - 1) * (1 : ℝ) * (1 + (Real.sqrt 2 - 1) + (1 : ℝ)) = 1 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith [h5]

    · -- Show that $t = (x + y) * (y + z)$
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

  · -- Show that 2 is minimal in the set
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, ht⟩

    nlinarith [sq_nonneg (y * (x + y + z) - x * z), sq_nonneg (x * z - y * (x + y + z)), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, sq_nonneg (y - (x + z)), sq_nonneg (x * y - z * (x + y + z)), sq_nonneg (x + y + z), sq_nonneg (x * z), sq_nonneg (y * (x + y + z) - 1)]