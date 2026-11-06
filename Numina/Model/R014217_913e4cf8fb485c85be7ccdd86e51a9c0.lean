import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_318167 :
  IsLeast {k : ℝ | ∃ x y, k = x + y + x * y ∧ 2 * x ^ 2 + 3 * x * y + 2 * y ^ 2 = 1} (-9 / 8) := by
  constructor
  · -- Show that -9/8 is in the set.
    use (-1 + Real.sqrt 57) / 8, (-1 - Real.sqrt 57) / 8
    constructor
    · -- Show that k = -9/8.
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 57 by norm_num : (57 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 57 by norm_num : (57 : ℝ) ≥ 0)]
    · -- Show that 2 * x^2 + 3 * x * y + 2 * y^2 = 1.
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 57 by norm_num : (57 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 57 by norm_num : (57 : ℝ) ≥ 0)]
  · -- Show that -9/8 is the least element.
    intro k
    rintro ⟨x, y, hk, h⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 1 / 4), sq_nonneg (x * y + 7 / 8), sq_nonneg (2 * x + 2 * y + 1)]