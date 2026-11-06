import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_316975 :
  IsLeast {z : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ 19/x + 98/y = 1 ∧ z = x + y} (117 + 14*Real.sqrt 38) := by
  constructor
  · -- Show (117 +14√38) is in the set.
    use 19 +7 * Real.sqrt 38, 98 +7 * Real.sqrt 38
    constructor
    · -- Show x >0
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (38 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (38 : ℝ) by norm_num)]
    constructor
    · -- Show y >0
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (38 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (38 : ℝ) by norm_num)]
    constructor
    · -- Show 19/x + 98/y = 1
      field_simp
      nlinarith [Real.sqrt_nonneg (38 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (38 : ℝ) by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (38 : ℝ) by norm_num)), sq_nonneg (Real.sqrt 38 - 0)]
    · -- Show z = x + y
      linarith [Real.sqrt_nonneg (38 : ℝ), Real.sqrt_nonneg (38 : ℝ)]
  · -- Show (117 +14√38) is the least
    intro z hz
    rcases hz with ⟨x, y, hx, hy, h_eq, hz⟩
    have h1 : 19 * y + 98 * x = x * y := by
      field_simp at h_eq
      linarith
    nlinarith [sq_nonneg (x - (19 +7 * Real.sqrt 38)), sq_nonneg (y - (98 +7 * Real.sqrt 38)), Real.sqrt_nonneg (38 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (38 : ℝ) by norm_num), mul_pos hx hy, sq_nonneg (x - y - 79), Real.sq_sqrt (show (0 : ℝ) ≤ (38 : ℝ) by norm_num), sq_nonneg (Real.sqrt 38 - 0)]